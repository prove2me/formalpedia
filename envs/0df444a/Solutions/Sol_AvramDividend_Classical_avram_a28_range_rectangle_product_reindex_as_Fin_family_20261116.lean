-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_range_rectangle_product_reindex_as_Fin_family_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:33:03.74723+00:00
-- url     : https://prove2.me/submissions/0dc0fb60-05fb-4e59-b5d7-bdac1609836d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
noncomputable section
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (n : ℕ) (Y : ℕ → Ω → E)
    (hFull : ∀ (A : ℕ → Set E),
      (∀ i < n, MeasurableSet (A i)) →
      P (⋂ i ∈ Finset.range n, Y i ⁻¹' A i) =
        ∏ i ∈ Finset.range n, P (Y i ⁻¹' A i)) :
    ∀ (A : Fin n → Set E), (∀ i, MeasurableSet (A i)) →
      P {ω : Ω | ∀ i : Fin n, Y i.val ω ∈ A i} =
        ∏ i : Fin n, P (Y i.val ⁻¹' A i) := by
  classical
  intro A hA
  let B : ℕ → Set E := fun i => if hi : i < n then A ⟨i, hi⟩ else Set.univ
  have hB : ∀ i < n, MeasurableSet (B i) := by
    intro i hi
    simpa only [B, dif_pos hi] using hA ⟨i, hi⟩
  have hEq := hFull B hB
  have hSet :
      {ω : Ω | ∀ i : Fin n, Y i.val ω ∈ A i} =
        (⋂ i ∈ Finset.range n, Y i ⁻¹' B i) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h i hi
      simpa only [B, dif_pos (Finset.mem_range.mp hi)] using
        h ⟨i, Finset.mem_range.mp hi⟩
    · intro h i
      simpa only [B, dif_pos i.isLt] using
        h i.val (Finset.mem_range.mpr i.isLt)
  have hProd :
      (∏ i : Fin n, P (Y i.val ⁻¹' A i)) =
        ∏ i ∈ Finset.range n, P (Y i ⁻¹' B i) := by
    rw [Finset.prod_fin_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [dif_pos (Finset.mem_range.mp hi), B]
  calc
    P {ω : Ω | ∀ i : Fin n, Y i.val ω ∈ A i} =
        P (⋂ i ∈ Finset.range n, Y i ⁻¹' B i) := congrArg P hSet
    _ = ∏ i ∈ Finset.range n, P (Y i ⁻¹' B i) := hEq
    _ = ∏ i : Fin n, P (Y i.val ⁻¹' A i) := hProd.symm
