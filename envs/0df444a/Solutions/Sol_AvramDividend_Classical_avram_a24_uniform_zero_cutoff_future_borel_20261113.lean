-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_uniform_zero_cutoff_future_borel_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:36:04.433317+00:00
-- url     : https://prove2.me/submissions/9e7ac543-e84b-4bee-ac4a-d4192af8a928

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_largejump_future_borel_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every translated original cutoff-zero Gaussian residual increment has a common future-path Borel representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 (s + T) ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
  obtain ⟨J, hJ, hLarge⟩ :=
    avram_a24_uniform_largejump_future_borel_20261113 X hX hFinite T
  let W : (ℝ≥0 → ℝ) → ℝ := fun Y =>
    Y T - (T : ℝ) * X.c - J Y
  have hW : Measurable W :=
    ((measurable_pi_apply T).sub_const ((T : ℝ) * X.c)).sub hJ
  refine ⟨W, hW, ?_⟩
  have hSmall (u : ℝ≥0) (ω : Ω) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 u ω = 0 := by
    simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
  intro s ω
  change (X.X (s + T) ω - ((s + T : ℝ≥0) : ℝ) * X.c -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 (s + T) ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s + T) ω) -
    (X.X s ω - (s : ℝ) * X.c -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 s ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω) =
    (X.X (s + T) ω - X.X s ω) - (T : ℝ) * X.c -
      J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω)
  rw [hSmall (s + T) ω, hSmall s ω]
  rw [← hLarge s ω, NNReal.coe_add]
  ring
