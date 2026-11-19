-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:08:15.785462+00:00
-- url     : https://prove2.me/submissions/db9e70c1-ab29-427c-a6fc-a3c402c2bd67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_compact_horizon_maximal_L1
import Theorems.Thm_AvramDividend_Classical_avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
import Theorems.Thm_AvramDividend_Classical_avram_j18_original_bounded_band_rightcont_optional_sampling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- The physical Gaussian compact-horizon maximal envelope gives bounded-stop optional sampling. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    Integrable (fun ω => R (τ ω) ω) P ∧
      P[(fun ω => R (τ ω) ω) | 𝓕.rightCont 0] =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
  obtain ⟨B, hBI, hDom⟩ :=
    avram_ja18_intrinsic_gaussian_compact_horizon_maximal_L1
      X hX hFinite R hR n hn
  have hContinuous :
      ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => R t ω) :=
    avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
      X hFinite R hR
  have hRight :
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => R u ω) (Set.Ici t) t := by
    filter_upwards [hContinuous] with ω hω
    intro t
    exact hω.continuousAt.continuousWithinAt
  have hZero : ∀ᵐ ω ∂P, R 0 ω = 0 :=
    avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
      X R hR
  exact avram_j18_original_bounded_band_rightcont_optional_sampling
    X hX hFinite n hn τ hτstop hτbound
    R B hRint hRmart hRight hZero hBI hDom
