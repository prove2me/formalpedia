-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_original_zero_nu_process_from_finite_jump_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:27:01.818765+00:00
-- url     : https://prove2.me/submissions/d0410db0-2f6b-40fd-bca1-cbbbf090007f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
import Theorems.Thm_AvramDividend_Classical_avram_ja19_same_filtration_zero_nu_from_intrinsic_gaussian_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original finite-activity zero-jump source follows from the intrinsic R construction and original-limit splitting. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hSource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∃ (Y : SpectrallyNegativeLevy P 𝓕),
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
          (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω) := by
  obtain ⟨R, hLimit, _hAdapt⟩ :=
    avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted X hFinite
  have hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) := by
    filter_upwards [hLimit] with ω hω
    exact hω.1
  obtain ⟨Y, hNu, hSigma, hYR⟩ :=
    avram_ja19_same_filtration_zero_nu_from_intrinsic_gaussian_limit
      X hX hFinite R hR
  have hSplit :=
    avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
      X R Jsmall hR hSource
  refine ⟨Y, hNu, hSigma, ?_⟩
  filter_upwards [hSplit, hYR] with ω hSplitω hYRω
  intro t
  calc
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        R t ω + Jsmall t ω := hSplitω t
    _ = (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω := by
      rw [hYRω t]
