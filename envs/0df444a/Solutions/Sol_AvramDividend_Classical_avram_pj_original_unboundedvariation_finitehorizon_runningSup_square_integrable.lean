-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:51:13.331285+00:00
-- url     : https://prove2.me/submissions/7a8f9346-30cb-40ce-8d0f-79d8d181246d

import Mathlib
import Mathlib.Probability.Moments.IntegrableExpMul
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the genuine original spectrally negative Lévy path, the running
supremum on every fixed finite horizon has a finite quadratic moment.
The proof uses the existing exact one-sided all-θ exponential moment
bound and the nonnegativity of the original supremum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (n : ℝ≥0) :
    Integrable (fun ω : Ω => (runningSup X n ω)^2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hPos : Integrable
      (fun ω : Ω => Real.exp (1 * runningSup X n ω)) P :=
    avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
      X hBV 1 (by norm_num) n
  have hSmeas : Measurable (fun ω : Ω => runningSup X n ω) := by
    have hT : Measurable (fun ω : Ω => (n, ω)) := by fun_prop
    exact (levy_runningSup_joint_time_path_measurable X).comp hT
  have hNeg : Integrable
      (fun ω : Ω => Real.exp (-(1 : ℝ) * runningSup X n ω)) P := by
    have hm : AEStronglyMeasurable
        (fun ω : Ω => Real.exp (-(1 : ℝ) * runningSup X n ω)) P :=
      (Real.continuous_exp.measurable.comp
        ((measurable_const :
          Measurable (fun _ : Ω => (-1 : ℝ))).mul hSmeas)).aestronglyMeasurable
    apply Integrable.of_bound hm 1
    filter_upwards [] with ω
    have hz : 0 ≤ runningSup X n ω :=
      (runningSup_eq_rawSup_nonneg X n ω).2
    have he : Real.exp (-(1 : ℝ) * runningSup X n ω) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using he
  have hSquare := integrable_pow_of_integrable_exp_mul
    (X := fun ω : Ω => runningSup X n ω) (μ := P)
    (t := (1 : ℝ)) (by norm_num) hPos hNeg 2
  simpa only [one_mul] using hSquare
