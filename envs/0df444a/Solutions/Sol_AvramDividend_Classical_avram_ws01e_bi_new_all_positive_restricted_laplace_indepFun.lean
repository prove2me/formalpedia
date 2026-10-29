-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_all_positive_restricted_laplace_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:03:30.759042+00:00
-- url     : https://prove2.me/submissions/c30c3423-4bac-44dc-a01f-b442a0fa99fb

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_nonneg_conditional_laplace_indepFun
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_restricted_real_integral_factor_conditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Every positive upper-ray Laplace factor identifies the full drawdown law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R D : Ω → ℝ) (hR : Measurable R) (hD : Measurable D)
    (hDnonneg : ∀ ω, 0 ≤ D ω)
    (hFactor : ∀ a β : ℝ, 0 < β →
      (∫⁻ ω in R ⁻¹' Set.Ioi a,
          ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P) =
        P (R ⁻¹' Set.Ioi a) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P)) :
    IndepFun R D P := by
  apply AvramDividend.Classical.avram_ws01e_bi_new_nonneg_conditional_laplace_indepFun
    P R D hR hD hDnonneg
  intro a ha β hβ
  let A : Set Ω := R ⁻¹' Set.Ioi a
  have hA : MeasurableSet A := hR measurableSet_Ioi
  haveI : IsProbabilityMeasure (P[|A]) :=
    ProbabilityTheory.cond_isProbabilityMeasure ha
  have hbound (ω : Ω) : ‖Real.exp (-(β * D ω))‖ ≤ (1 : ℝ) := by
    have hmul : 0 ≤ β * D ω := mul_nonneg hβ.le (hDnonneg ω)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmul)
  have hf : Measurable (fun ω : Ω => Real.exp (-(β * D ω))) := by fun_prop
  have hfP : AEStronglyMeasurable (fun ω : Ω => Real.exp (-(β * D ω))) P :=
    hf.aestronglyMeasurable
  have hfA : AEStronglyMeasurable (fun ω : Ω => Real.exp (-(β * D ω))) (P[|A]) :=
    hf.aestronglyMeasurable
  have hIntP : Integrable (fun ω : Ω => Real.exp (-(β * D ω))) P :=
    Integrable.of_bound hfP 1 (ae_of_all _ hbound)
  have hIntA : Integrable (fun ω : Ω => Real.exp (-(β * D ω))) (P[|A]) :=
    Integrable.of_bound hfA 1 (ae_of_all _ hbound)
  have hPos (ω : Ω) : 0 ≤ Real.exp (-(β * D ω)) :=
    (Real.exp_pos _).le
  have hFacA :
      (∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P) =
        P A * (∫⁻ ω, ENNReal.ofReal (Real.exp (-(β * D ω))) ∂P) :=
    hFactor a β hβ
  simpa only [A] using
    (AvramDividend.Classical.avram_ws01e_bi_new_restricted_real_integral_factor_conditional
      P A hA ha (fun ω => Real.exp (-(β * D ω))) hPos hIntP hIntA hFacA)
