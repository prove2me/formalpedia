-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18h_original_intrinsic_residual_increment_shift_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:34:24.024741+00:00
-- url     : https://prove2.me/submissions/40270b1a-1b02-4186-9958-1e9b0c7ad41e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_largejump_window_shift_borel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- At cutoff zero the small compensated band is empty; a Borel jump-window
factorisation therefore suffices for the original residual increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ ω : Ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by
  obtain ⟨J, hJ, hJsource⟩ :=
    avram_ja18h_original_largejump_window_shift_borel X hX hFinite s t hst
  let T : ℝ≥0 := t - s
  let W : (ℝ≥0 → ℝ) → ℝ := fun Y =>
    Y T - (T : ℝ) * X.c - J Y
  have hW : Measurable W :=
    ((measurable_pi_apply T).sub_const ((T : ℝ) * X.c)).sub hJ
  refine ⟨W, hW, ?_⟩
  have hSmall (u : ℝ≥0) (ω : Ω) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 u ω = 0 := by
    simp [avram_p4_h_gaussian_intrinsic_small_band_compensated]
  intro ω
  have ht : s + T = t := add_tsub_cancel_of_le hst
  have hT : (T : ℝ) = (t : ℝ) - (s : ℝ) := NNReal.coe_sub hst
  have hLarge := hJsource ω
  change (X.X t ω - (t : ℝ) * X.c -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) -
      (X.X s ω - (s : ℝ) * X.c -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 s ω -
      avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω) =
      (X.X (s + T) ω - X.X s ω) - (T : ℝ) * X.c -
      J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω)
  rw [hSmall t ω, hSmall s ω, ht]
  rw [← hLarge, hT]
  ring
