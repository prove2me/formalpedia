-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_raw_R_fixed_time_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:57:51.076975+00:00
-- url     : https://prove2.me/submissions/a470ec5e-1be7-4720-a3ef-1345424d3f4f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_X_integrable_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_raw_R_coordinate_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original drift remainder after subtracting the literal real raw jump
sum is integrable at every fixed horizon. Its nonnegative samplewise mass is
bounded by the genuine drift-minus-X endpoint, and X is L1 by Standing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) (T : ℝ≥0) :
    Integrable (fun ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ T then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let R : Ω → ℝ := fun ω =>
    ((T : ℝ) * X.drift - X.X T ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ T then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0)
  change Integrable R P
  have hMeas : AEStronglyMeasurable R P := by
    simpa only [R] using
      avram_a19_nonint_original_raw_R_coordinate_measurable X hX hBV T
  have hDom : ∀ᵐ ω ∂P, ‖R ω‖ ≤ (T : ℝ) * X.drift - X.X T ω := by
    filter_upwards [avram_bv_residual10_original_raw_R_ae_monotone X hBV]
      with ω hmono
    have hz :
        (((0 : ℝ≥0) : ℝ) * X.drift - X.X 0 ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ (0 : ℝ≥0) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) = 0 := by
      have hJ0 :
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ (0 : ℝ≥0) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) = 0 := by
        have hImpossible (v : ℝ≥0) :
            ¬ (0 < v ∧ v ≤ (0 : ℝ≥0)) := by
          intro hv
          exact not_lt_of_ge hv.2 hv.1
        have hZeroFun :
            (fun v : ℝ≥0 =>
              if 0 < v ∧ v ≤ (0 : ℝ≥0) then
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
              else (0 : ℝ)) = (fun _ => (0 : ℝ)) := by
          funext v
          exact if_neg (hImpossible v)
        rw [hZeroFun]
        simp
      rw [hJ0]
      simp [X.X_zero]
    have hnonneg : 0 ≤ R ω := by
      have h := hmono (show (0 : ℝ≥0) ≤ T from zero_le)
      change (((0 : ℝ≥0) : ℝ) * X.drift - X.X 0 ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ (0 : ℝ≥0) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) ≤ R ω at h
      simpa only [hz] using h
    have hJ : 0 ≤ (∑' v : ℝ≥0, if 0 < v ∧ v ≤ T then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) :=
      avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
        X ω 0 T (show (0 : ℝ≥0) ≤ T from zero_le)
    have hupper : R ω ≤ (T : ℝ) * X.drift - X.X T ω := by
      dsimp [R]
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hupper
  have hInt : Integrable (fun ω => (T : ℝ) * X.drift - X.X T ω) P :=
    (integrable_const _).sub
      (avram_p3_comp8_original_X_integrable_any_clock X hX hBV T)
  exact hInt.mono' hMeas hDom
