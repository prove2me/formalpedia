-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_nested_finite_L2_truncation_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:15:33.559494+00:00
-- url     : https://prove2.me/submissions/bc271a74-6740-4b45-9346-3952495c4e2b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_orthogonal_finite_L2_energy_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Nested finite compensated jump bands have a squared approximation error
controlled by the variance budget on the omitted bands, provided the
actual source increments are pairwise L2-orthogonal. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] {P : Measure Ω}
    (S T : Finset ι) (hST : S ⊆ T)
    (F : ι → Ω → ℝ) (v : ι → ℝ)
    (hProd : ∀ i ∈ T, ∀ j ∈ T,
      Integrable (fun ω => F i ω * F j ω) P)
    (hOrth : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      (∫ ω, F i ω * F j ω ∂P) = 0)
    (hVar : ∀ i ∈ T,
      (∫ ω, (F i ω)^2 ∂P) ≤ v i) :
    (∫ ω, ((∑ i ∈ T, F i ω) - (∑ i ∈ S, F i ω))^2 ∂P) ≤ (∑ i ∈ T \ S, v i) := by
  classical
  have hsum (ω : Ω) :
      (∑ i ∈ T, F i ω) - (∑ i ∈ S, F i ω) =
        ∑ i ∈ T \ S, F i ω := by
    have h := Finset.sum_sdiff (f := fun i => F i ω) hST
    linarith
  calc
    (∫ ω, ((∑ i ∈ T, F i ω) - (∑ i ∈ S, F i ω))^2 ∂P) =
        (∫ ω, (∑ i ∈ T \ S, F i ω)^2 ∂P) := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [hsum ω]
    _ ≤ (∑ i ∈ T \ S, v i) := by
      apply AvramDividend.Classical.avram_p4_b_smalljump_orthogonal_finite_L2_energy_bound
      · intro i hi j hj
        exact hProd i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1
      · intro i hi j hj hij
        exact hOrth i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1 hij
      · intro i hi
        exact hVar i (Finset.mem_sdiff.mp hi).1
