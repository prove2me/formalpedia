-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_actual_jump_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:55:31.689445+00:00
-- url     : https://prove2.me/submissions/3dfc9fb6-32cc-4caa-bae1-0a6f68ce87af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_total_aemeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original finite-horizon full negative-jump exponential is L1
for every nonnegative Laplace parameter, without jump moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω : Ω =>
      Real.exp (-(θ * (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal))) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let J : Ω → ℝ := fun ω =>
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T then
        ENNReal.ofReal (Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0).toReal
  have hJ : AEMeasurable J P :=
    avram_p3_a_bvdrift_actual_jump_total_aemeasurable X hBV T
  have hExpMeas : AEStronglyMeasurable (fun ω : Ω =>
      Real.exp (-(θ * J ω))) P := by
    have hm : Measurable (fun z : ℝ => Real.exp (-(θ * z))) := by fun_prop
    exact (hm.comp_aemeasurable hJ).aestronglyMeasurable
  change Integrable (fun ω : Ω => Real.exp (-(θ * J ω))) P
  apply Integrable.of_bound hExpMeas 1
  filter_upwards [] with ω
  have hJnonneg : 0 ≤ J ω := ENNReal.toReal_nonneg
  have hx : -(θ * J ω) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg hθ hJnonneg)
  have hh := Real.exp_le_exp.mpr hx
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.exp_zero] using hh
