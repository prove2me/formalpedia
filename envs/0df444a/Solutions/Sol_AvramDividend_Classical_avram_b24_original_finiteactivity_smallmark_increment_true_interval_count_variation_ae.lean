-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_smallmark_increment_true_interval_count_variation_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:42:07.09706+00:00
-- url     : https://prove2.me/submissions/678f3deb-e72c-496c-b2b0-d072af6dba22

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
import Theorems.Thm_AvramDividend_Classical_avram_b24_true_finite_smallnegative_mark_step_increment_le_interval_actual_jump_count
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
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      ∀ (s t : ℝ≥0), s ≤ t → t ≤ T →
        ‖Jsmall t ω - Jsmall s ω‖ ≤
        ((S.filter (fun u =>
          s < u ∧ u ≤ t ∧
          -1 < X.X u ω -
             Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
          X.X u ω -
             Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0)).card : ℝ) +
        ((t : ℝ) - (s : ℝ)) *
          ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖ := by
  have hHorizon :=
    AvramDividend.Classical.avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
      X hFinite Jsmall hJsource
  filter_upwards [hHorizon] with ω hω
  obtain ⟨S, hS, hPath⟩ := hω T
  refine ⟨S, hS, ?_⟩
  let z : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let d : ℝ := ∫ v in Ioo (-1 : ℝ) 0, v ∂X.ν
  intro s t hst htT
  have hsT : s ≤ T := le_trans hst htT
  have hStep :=
    AvramDividend.Classical.avram_b24_true_finite_smallnegative_mark_step_increment_le_interval_actual_jump_count
      S z s t hst
  have hT (v : ℝ≥0) (hv : v ≤ T) :
      Jsmall v ω =
        (∑ u ∈ S, if u ≤ v then
          (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (v : ℝ) * d := by
    simpa only [z, d] using hPath v hv
  change ‖Jsmall t ω - Jsmall s ω‖ ≤
      ((S.filter (fun u => s < u ∧ u ≤ t ∧
        -1 < z u ∧ z u < 0)).card : ℝ) +
      ((t : ℝ) - (s : ℝ)) * ‖d‖
  have hDur : (0 : ℝ) ≤ (t : ℝ) - (s : ℝ) := by
    have htReal : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    linarith
  calc
    ‖Jsmall t ω - Jsmall s ω‖ =
      ‖(∑ u ∈ S, if u ≤ t then
          (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (∑ u ∈ S, if u ≤ s then
          (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        ((t : ℝ) - (s : ℝ)) * d‖ := by
        rw [hT t htT, hT s hsT]
        congr 1
        ring
    _ ≤
      ‖(∑ u ∈ S, if u ≤ t then
          (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (∑ u ∈ S, if u ≤ s then
          (if -1 < z u ∧ z u < 0 then z u else 0) else 0)‖ +
      ‖((t : ℝ) - (s : ℝ)) * d‖ :=
      norm_sub_le _ _
    _ ≤ ((S.filter (fun u => s < u ∧ u ≤ t ∧
        -1 < z u ∧ z u < 0)).card : ℝ) +
        ((t : ℝ) - (s : ℝ)) * ‖d‖ := by
      have hDurNorm : ‖(t : ℝ) - (s : ℝ)‖ =
          (t : ℝ) - (s : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hDur]
      rw [norm_mul, hDurNorm]
      exact add_le_add hStep le_rfl
