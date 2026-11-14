-- Prove2me | solution 4 for AvramDividend.Classical.avram_ja18i_original_zero_cutoff_gaussian_square_integrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:56:30.1562+00:00
-- url     : https://prove2.me/submissions/6f61d856-4935-4203-a80b-08ba3c5dd647
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_finite_activity_smallband_limit_square_L1
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_exact_square_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
import Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual zero-cutoff source has finite square moment from the physical Gaussian and compensated band limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (t : ℝ≥0), Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) P := by
  obtain ⟨R, hLimit, _hAdapt⟩ :=
    avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted X hFinite
  obtain ⟨Jsmall, hJ, hJL2⟩ :=
    avram_ja19_original_finite_activity_smallband_limit_square_L1 X hX hFinite
  have hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)) := by
    filter_upwards [hLimit] with ω hω
    exact hω.1
  have hDecomp :=
    avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
      X R Jsmall hRsource hJ
  intro t
  have hf : AEStronglyMeasurable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) P :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X 0 t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  have hG :=
    (avram_ja22_original_limit_gaussian_exact_square_moment
      X hX hFinite R hRsource t).1
  have heq : ∀ᵐ ω ∂P,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
        R t ω + Jsmall t ω := by
    filter_upwards [hDecomp] with ω hω
    exact hω t
  exact avram_ja19_square_integrable_of_ae_sum_components
    (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω)
    (R t) (Jsmall t) hf hG (hJL2 t) heq
