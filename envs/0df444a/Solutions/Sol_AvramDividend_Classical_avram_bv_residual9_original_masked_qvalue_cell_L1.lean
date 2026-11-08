-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_masked_qvalue_cell_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:01:46.078741+00:00
-- url     : https://prove2.me/submissions/b2871155-c8f3-4345-9340-2fa3dc0d50bb

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_leftlim_value_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact stopped interior grid mask preserves L1 of the discount-weighted
q*w pre-jump value term. Generator and compensated R terms are separate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T t : ℝ≥0) (ht : t ≤ T) (C : ℝ≥0∞) :
    Integrable (fun ω =>
      let Z : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      if (t : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (t : ℝ))) * (q * w Z)
      else 0) P := by
  let Z : Ω → ℝ := fun ω => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let E : Set Ω := {ω |
    (t : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z ω ∧ ENNReal.ofReal (Z ω) < C}
  have hZ : Measurable Z :=
    (avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
      X x D hD).comp (measurable_const.prodMk measurable_id)
  have hRuin : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD
  have hE : MeasurableSet E := by
    have h1 : MeasurableSet {ω : Ω |
        (t : ℝ≥0∞) < ruinTime X x D ω} :=
      measurableSet_lt measurable_const hRuin
    have h2 : MeasurableSet {ω : Ω | 0 < Z ω} :=
      measurableSet_lt measurable_const hZ
    have h3 : MeasurableSet {ω : Ω |
        ENNReal.ofReal (Z ω) < C} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp hZ) measurable_const
    exact h1.inter (h2.inter h3)
  have hValue : Integrable (fun ω => w (Z ω)) P :=
    avram_bv_residual9_original_global_leftlim_value_L1_auto
      X hBV x D hD w hw_cont hw_neg T t ht
  have hCoeff : Integrable (fun ω =>
      Real.exp (-(q * (t : ℝ))) * (q * w (Z ω))) P := by
    simpa only [mul_assoc] using
      (hValue.const_mul (Real.exp (-(q * (t : ℝ))) * q))
  have hw : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hCoeffMeas : Measurable (fun ω : Ω =>
      Real.exp (-(q * (t : ℝ))) * (q * w (Z ω))) :=
    measurable_const.mul (measurable_const.mul (hw.comp hZ))
  have hMaskedMeas : AEStronglyMeasurable
      (fun ω => if ω ∈ E then
        Real.exp (-(q * (t : ℝ))) * (q * w (Z ω))
       else 0) P :=
    (Measurable.ite hE hCoeffMeas measurable_const).aestronglyMeasurable
  have hInt : Integrable (fun ω => if ω ∈ E then
      Real.exp (-(q * (t : ℝ))) * (q * w (Z ω)) else 0) P := by
    refine hCoeff.norm.mono' hMaskedMeas ?_
    filter_upwards [] with ω
    by_cases hω : ω ∈ E
    · simp [hω]
    · simpa only [if_neg hω, norm_zero] using
        (norm_nonneg (Real.exp (-(q * (t : ℝ))) * (q * w (Z ω))))
  simpa [E, Z] using hInt
