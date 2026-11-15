-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_smallmark_actual_finite_jump_path_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:21:43.251051+00:00
-- url     : https://prove2.me/submissions/1bd01cb3-56d2-482d-af7f-8de161ba24ec

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
import Theorems.Thm_AvramDividend_Classical_avram_b24_finite_original_negative_mark_cutoff_sum_eventual_exact_limit
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallband_mark_path_from_finite_jump_cutoff_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
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
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ∃ S : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
        Jsmall t ω =
          (∑ u ∈ S,
            if -1 < X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
            then X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
            else 0) -
          (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)  := by
  filter_upwards [hJsource,
    avram_a30_original_finiteactivity_physical_jump_sum_cadlag_on_each_horizon_20261114
      X hFinite] with ω hJ hS
  intro t
  obtain ⟨S, hST, _, _, _⟩ := hS t
  refine ⟨S, hST, ?_⟩
  have hCut :=
    avram_b24_finite_original_negative_mark_cutoff_sum_eventual_exact_limit S
      (fun u => X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  exact avram_b24_original_smallband_mark_path_from_finite_jump_cutoff_limit
    X hFinite ω t Jsmall (hJ t) S hST hCut
