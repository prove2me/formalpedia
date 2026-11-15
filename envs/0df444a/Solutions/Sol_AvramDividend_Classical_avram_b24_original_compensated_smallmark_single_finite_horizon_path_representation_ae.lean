-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:31:03.602964+00:00
-- url     : https://prove2.me/submissions/1b540be7-1bbe-4ad0-9ab9-527273ada4e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_intrinsic_smallmark_actual_finite_jump_path_ae
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_true_jump_support_reuse_horizon_for_all_earlier_mark_sums
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ S : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
        ∀ t : ℝ≥0, t ≤ T →
          Jsmall t ω =
            (∑ u ∈ S, if u ≤ t then
              (if -1 < X.X u ω -
                   Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
                  X.X u ω -
                   Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
               then X.X u ω -
                   Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0)
             else 0) -
            (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) := by
  have hSupport :=
    avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
      X hFinite
  have hPath :=
    avram_b24_original_finiteactivity_intrinsic_smallmark_actual_finite_jump_path_ae
      X hFinite Jsmall hJsource
  filter_upwards [hSupport, hPath] with ω hSω hPω
  intro T
  obtain ⟨S, hS, hRC, hLC, hJump⟩ := hSω T
  refine ⟨S, hS, ?_⟩
  intro t ht
  obtain ⟨St, hSt, hFormula⟩ := hPω t
  have hIdentity :=
    avram_b24_original_true_jump_support_reuse_horizon_for_all_earlier_mark_sums
      S St (fun u : ℝ≥0 =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      T t ht hS hSt
  rw [hFormula]
  rw [hIdentity]
