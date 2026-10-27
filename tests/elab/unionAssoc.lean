module

import Std.Data

/-! Check union associativity across hash/tree maps, sets, and Raw variants, using the weakest
comparison assumptions and preserving right-biased values for overlapping keys. -/

open Std

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : DHashMap α β} :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  DHashMap.union_assoc_equiv

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : ExtDHashMap α β} :
    (m₁ ∪ m₂) ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) :=
  ExtDHashMap.union_assoc

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashMap α β} :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  HashMap.union_assoc_equiv

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : ExtHashMap α β} :
    (m₁ ∪ m₂) ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) :=
  ExtHashMap.union_assoc

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashSet α} :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  HashSet.union_assoc_equiv

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : ExtHashSet α} :
    (m₁ ∪ m₂) ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) :=
  ExtHashSet.union_assoc

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : DHashMap.Raw α β}
    (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  DHashMap.Raw.union_assoc_equiv h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashMap.Raw α β}
    (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  HashMap.Raw.union_assoc_equiv h₁ h₂ h₃

example [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ m₃ : HashSet.Raw α}
    (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  HashSet.Raw.union_assoc_equiv h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp] {m₁ m₂ m₃ : DTreeMap α β cmp} :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  DTreeMap.union_assoc_equiv

example {cmp : α → α → Ordering} [TransCmp cmp] {m₁ m₂ m₃ : ExtDTreeMap α β cmp} :
    (m₁ ∪ m₂) ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) :=
  ExtDTreeMap.union_assoc

example {cmp : α → α → Ordering} [TransCmp cmp] {m₁ m₂ m₃ : TreeMap α β cmp} :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  TreeMap.union_assoc_equiv

example {cmp : α → α → Ordering} [TransCmp cmp] {m₁ m₂ m₃ : ExtTreeMap α β cmp} :
    (m₁ ∪ m₂) ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) :=
  ExtTreeMap.union_assoc

example {cmp : α → α → Ordering} [TransCmp cmp] {m₁ m₂ m₃ : TreeSet α cmp} :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  TreeSet.union_assoc_equiv

example {cmp : α → α → Ordering} [TransCmp cmp] {m₁ m₂ m₃ : ExtTreeSet α cmp} :
    (m₁ ∪ m₂) ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) :=
  ExtTreeSet.union_assoc

example {cmp : α → α → Ordering} [TransCmp cmp] {m₁ m₂ m₃ : DTreeMap.Raw α β cmp}
    (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  DTreeMap.Raw.union_assoc_equiv h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp] {m₁ m₂ m₃ : TreeMap.Raw α β cmp}
    (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  TreeMap.Raw.union_assoc_equiv h₁ h₂ h₃

example {cmp : α → α → Ordering} [TransCmp cmp] {m₁ m₂ m₃ : TreeSet.Raw α cmp}
    (h₁ : m₁.WF) (h₂ : m₂.WF) (h₃ : m₃.WF) :
    ((m₁ ∪ m₂) ∪ m₃).Equiv (m₁ ∪ (m₂ ∪ m₃)) :=
  TreeSet.Raw.union_assoc_equiv h₁ h₂ h₃

example (a b c : ExtHashMap Nat Nat) : ((a ∪ b) ∪ c)[0]? = c[0]?.or (b[0]?.or a[0]?) := by
  rw [ExtHashMap.union_assoc, ExtHashMap.getElem?_union, ExtHashMap.getElem?_union]
  exact Option.or_assoc

example : ((({(0, 10)} : ExtHashMap Nat Nat) ∪ {(0, 20)}) ∪ {(0, 30)})[0]? = some 30 := by
  rw [ExtHashMap.union_assoc]
  simp only [ExtHashMap.getElem?_union, ExtHashMap.singleton_eq_insert,
    ExtHashMap.getElem?_insert_self, Option.some_or]
