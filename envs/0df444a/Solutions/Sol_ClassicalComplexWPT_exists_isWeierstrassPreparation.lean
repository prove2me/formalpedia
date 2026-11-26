-- Prove2me | solution 1 for ClassicalComplexWPT.exists_isWeierstrassPreparation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:37:56.439181+00:00
-- url     : https://prove2.me/submissions/8921e552-4087-407d-8a47-f37d3bfb294e

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_zero
import Theorems.Thm_ClassicalComplexWPT_analyticAt_preparationCoefficient
import Theorems.Thm_ClassicalComplexWPT_preparationCoefficient_zero
import Theorems.Thm_ClassicalComplexWPT_analyticAt_preparationQuotientEval
import Theorems.Thm_ClassicalComplexWPT_preparationQuotientEval_zero
import Theorems.Thm_ClassicalComplexWPT_analyticAt_preparationUnit
import Theorems.Thm_ClassicalComplexWPT_preparationUnit_zero_ne
import Theorems.Thm_ClassicalComplexWPT_preparation_factorization_of_sequence_factorization
import Theorems.Thm_ClassicalComplexWPT_ambient_zero_eq
import Theorems.Thm_ClassicalComplexWPT_eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
import Theorems.Thm_ClassicalComplexWPT_exists_normalizedPreparationSequences
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainder
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainderGlobal
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply
attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionOperatorInput_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionRhsInput_apply
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainder
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainderGlobal
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.evalL1PowerSeries_zero

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ),
      IsWeierstrassPreparation f d a u := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨r, hr, hr0, htop, hq, hrem, hfac, hrem0, hq0⟩ :=
    exists_normalizedPreparationSequences p hp horder
  let a : Fin d → Base n → ℂ := preparationCoefficient p r hr d
  let u : Ambient n → ℂ := preparationUnit p r hr d
  refine ⟨a, u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact analyticAt_preparationCoefficient p r hr d hrem i
  · intro i
    exact preparationCoefficient_zero p r hr d hrem0 i
  · exact analyticAt_preparationUnit p r hr d hq hq0
  · exact preparationUnit_zero_ne p r hr d hr0 htop hq0
  · have hfac' : ∀ᶠ x : Ambient n in 𝓝 0,
        monomialSeq d = convolution (normalizedPreparationQuotient p r hr d x.1)
            (analyticNormalizedCoefficientMap p r hr d x.1) +
              normalizedPreparationRemainder p r hr d x.1 ∧
        seqHighShift d (normalizedPreparationRemainder p r hr d x.1) = 0 :=
      (continuousAt_fst : ContinuousAt (fun x : Ambient n ↦ x.1) 0).eventually hfac
    have hrecon :=
      eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
        p r hp hr0 hr
    have hscaled : ∀ᶠ x : Ambient n in 𝓝 0, ‖(r : ℂ)⁻¹ * x.2‖ < 1 := by
      have hc : ContinuousAt (fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2) 0 := by
        fun_prop
      have hb := Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
      have hb' : Metric.ball (0 : ℂ) 1 ∈
          nhds ((fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2) 0) := by
        simpa [ambient_zero_eq] using hb
      have he := hc.eventually hb'
      simpa only [Metric.mem_ball, dist_zero_right] using he
    have hQne : ∀ᶠ x : Ambient n in 𝓝 0,
        preparationQuotientEval p r hr d x ≠ 0 := by
      have hQa := analyticAt_preparationQuotientEval p r hr d hq
      apply hQa.continuousAt.eventually_ne
      rw [preparationQuotientEval_zero, hq0]
      exact one_ne_zero
    filter_upwards [hfac', hrecon, hscaled, hQne] with x hx hrec hxw hxQ
    simpa only [a, u] using
      preparation_factorization_of_sequence_factorization p r hr hr0 htop
        x.1 x.2 hx.1 hx.2 hxw hrec hxQ
end ClassicalComplexWPT
