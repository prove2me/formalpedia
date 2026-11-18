-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_admissible_disjoint_union_functional_finite_product_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:25:01.468747+00:00
-- url     : https://prove2.me/submissions/245cecca-f31b-49e0-b530-dfbd50b137c7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- A disjoint-union multiplicative functional factors over admissible finite families. -/
theorem solution
    {α ι : Type*} [DecidableEq ι]
    (Good : Set α → Prop) (B : ι → Set α) (Q : Set α → ℝ)
    (hEmpty : Q ∅ = 1)
    (hGoodUnion : ∀ S : Finset ι,
      (∀ i ∈ S, Good (B i)) → Good (⋃ i ∈ S, B i))
    (hMul : ∀ U V : Set α,
      Good U → Good V → Disjoint U V →
        Q (U ∪ V) = Q U * Q V) :
    ∀ S : Finset ι,
      (∀ i ∈ S, Good (B i)) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        Disjoint (B i) (B j)) →
      Q (⋃ i ∈ S, B i) = ∏ i ∈ S, Q (B i) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _ _
      simpa using hEmpty
  | @insert a S ha ih =>
      intro hGood hPair
      have hGa : Good (B a) :=
        hGood a (Finset.mem_insert_self a S)
      have hGS : ∀ i ∈ S, Good (B i) := by
        intro i hi
        exact hGood i (Finset.mem_insert_of_mem hi)
      have hPS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
          Disjoint (B i) (B j) := by
        intro i hi j hj hNe
        exact hPair i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hNe
      have hDU : Disjoint (B a) (⋃ i ∈ S, B i) := by
        apply Set.disjoint_left.mpr
        intro x hx hxU
        rcases Set.mem_iUnion.mp hxU with ⟨i, hi⟩
        rcases Set.mem_iUnion.mp hi with ⟨hiS, hiB⟩
        have hNe : a ≠ i := by
          intro h
          subst i
          exact ha hiS
        exact (Set.disjoint_left.mp
          (hPair a (Finset.mem_insert_self a S)
            i (Finset.mem_insert_of_mem hiS) hNe)) hx hiB
      calc
        Q (⋃ i ∈ insert a S, B i) =
            Q (B a ∪ (⋃ i ∈ S, B i)) := by
              simp [Finset.set_biUnion_insert]
        _ = Q (B a) * Q (⋃ i ∈ S, B i) :=
          hMul (B a) (⋃ i ∈ S, B i)
            hGa (hGoodUnion S hGS) hDU
        _ = Q (B a) * ∏ i ∈ S, Q (B i) := by
          rw [ih hGS hPS]
        _ = ∏ i ∈ insert a S, Q (B i) := by
          simp [Finset.prod_insert, ha]
