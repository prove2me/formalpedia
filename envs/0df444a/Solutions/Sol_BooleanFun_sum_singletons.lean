-- Prove2me | solution 1 for BooleanFun.sum_singletons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:58:54.198185+00:00
-- url     : https://prove2.me/submissions/299afae6-4203-46c3-872a-abc3a3957e7a

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary

set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]
namespace BooleanFun
theorem _root_.solution [AddCommMonoid α] {F : Finset ι → α} {G : ι → α} (h : ∀ i, F {i} = G i):
    ∑ S ∈ {S|S.card = 1}, F S = ∑ i, G i := by {
  symm
  apply sum_of_injOn (e := fun i ↦ {i})
  -- injective
  · intro j _ l _ h
    dsimp at h
    apply eq_of_mem_singleton
    rw [← h]
    exact mem_singleton_self j
-- maps into correct set
  · intro j _
    simp
-- ets : surjective
  · intro S hS hS'
    simp at hS
    obtain ⟨i, hi⟩ := card_eq_one.mp hS
    simp at hS'
    tauto
-- summands equal
  · intro i _
    symm
    exact h i
}
end BooleanFun
