-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_residual_eq_two_finite_jump_sums
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:32:20.25971+00:00
-- url     : https://prove2.me/submissions/fc11b65e-6d4d-4b07-b1cf-3b64da1bd0f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Every original cutoff residual is literally the source path minus its
finite small and large jump sums and deterministic Levy compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (T : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ F G : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1))) ∧
      (∀ u : ℝ≥0, u ∈ G ↔ 0 < u ∧ u ≤ T ∧ j u ≤ -1) ∧
      avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω =
        X.X T ω - (T : ℝ) * X.c -
          ((∑ u ∈ F, j u) -
             (T : ℝ) * (∫ z in Ioc (-1 : ℝ)
                (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) -
          (∑ u ∈ G, j u) := by
  intro j
  classical
  obtain ⟨F, hF, hSmall⟩ :=
    avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
      X ω T n
  obtain ⟨G, hG, hLarge⟩ :=
    avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
      X ω T
  refine ⟨F, G, hF, hG, ?_⟩
  simp only [avram_p4_h_gaussian_intrinsic_truncated_residual,
    avram_p4_h_gaussian_intrinsic_small_band_compensated]
  rw [hSmall, hLarge]
