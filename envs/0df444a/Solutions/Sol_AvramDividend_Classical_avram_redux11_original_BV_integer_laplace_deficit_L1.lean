-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux11_original_BV_integer_laplace_deficit_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:24:16.800898+00:00
-- url     : https://prove2.me/submissions/b214d757-8466-4bf5-832f-7f6e34131421

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_total_aemeasurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_canonical_residual_nonnegative_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
      let R : ℝ≥0 → Ω → ℝ := fun t ω =>
        (((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))
      ∀ n : ℕ, Integrable
        (fun ω => 1 - Real.exp (-(R (n : ℝ≥0) ω))) P  := by
  dsimp only
  intro n
  letI : IsProbabilityMeasure P := X.isProbability
  let Jc : Ω → ℝ := fun ω =>
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ (n : ℝ≥0) then
      ENNReal.ofReal
        (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
      else 0).toReal
  let Jr : Ω → ℝ := fun ω =>
    ∑' u : ℝ≥0, if 0 < u ∧ u ≤ (n : ℝ≥0) then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0
  let R : Ω → ℝ := fun ω =>
    ((n : ℝ) * X.drift - X.X (n : ℝ≥0) ω) - Jr ω
  change Integrable (fun ω : Ω => 1 - Real.exp (-(R ω))) P
  have hsum := avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV
  have hEq : Jc =ᵐ[P] Jr := by
    filter_upwards [hsum] with ω hw
    exact (hw 0 (n : ℝ≥0) (by positivity)).2
  have hJc : AEMeasurable Jc P :=
    avram_p3_a_bvdrift_actual_jump_total_aemeasurable X hBV n
  have hJr : AEMeasurable Jr P := hJc.congr hEq
  have hLap : Integrable
      (fun ω : Ω => Real.exp (X.X (n : ℝ≥0) ω)) P := by
    simpa only [one_mul] using (X.laplace (n : ℝ≥0) 1 (by norm_num)).1
  have hExpMeas : AEMeasurable
      (fun ω : Ω => Real.exp (X.X (n : ℝ≥0) ω)) P :=
    hLap.aestronglyMeasurable.aemeasurable
  have hXMeas : AEMeasurable (fun ω : Ω => X.X (n : ℝ≥0) ω) P := by
    simpa only [Function.comp_def, Real.log_exp] using
      (Real.measurable_log.comp_aemeasurable hExpMeas)
  have hRMeas : AEMeasurable R P := by
    exact (aemeasurable_const.sub hXMeas).sub hJr
  have hMeas : AEStronglyMeasurable
      (fun ω : Ω => 1 - Real.exp (-(R ω))) P := by
    have hm : Measurable (fun z : ℝ => 1 - Real.exp (-z)) := by fun_prop
    exact (hm.comp_aemeasurable hRMeas).aestronglyMeasurable
  have hPos := avram_p3_a_bvdrift_original_canonical_residual_nonnegative_time X hBV
  have hRPos : ∀ᵐ ω ∂P, 0 ≤ R ω := by
    filter_upwards [hPos, hEq] with ω hp heq
    dsimp [R]
    rw [← heq]
    exact hp (n : ℝ≥0)
  apply Integrable.of_bound hMeas 1
  filter_upwards [hRPos] with ω hω
  have hb : Real.exp (-(R ω)) ≤ 1 := by
    have hh : -(R ω) ≤ 0 := neg_nonpos.mpr hω
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hh)
  have he : 0 < Real.exp (-(R ω)) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hb)]
  linarith
