-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_ibp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:16.279431+00:00
-- url     : https://prove2.me/submissions/145889c7-632c-440e-9377-759086ecf100

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_clm_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_hasFDerivAt_osc
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_contDiff_osc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {φ : E → ℝ} (τ : ℝ) (hφ : ContDiff ℝ 1 φ) {c : E → V} (hc : ContDiff ℝ 1 c)
    (hcs : HasCompactSupport c) (v : E) :
    ∫ x, osc φ τ x • fderiv ℝ c x v ∂μ =
      -∫ x, (Complex.I * osc φ τ x * ((τ⁻¹ * fderiv ℝ φ x v : ℝ) : ℂ)) • c x ∂μ := by
  have hoc : Continuous (osc φ τ) := (B_contDiff_osc τ hφ).continuous
  have hφ' : Continuous (fun x => fderiv ℝ φ x v) := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hc' : Continuous (fun x => fderiv ℝ c x v) := (hc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := μ)
    (f := osc φ τ) (f' := fun x => Complex.I * osc φ τ x * ((τ⁻¹ * fderiv ℝ φ x v : ℝ) : ℂ))
    (g := c) (g' := fun x => fderiv ℝ c x v) (v := v) (B := ContinuousLinearMap.lsmul ℝ ℂ) ?_ ?_ ?_ ?_ ?_
  · simpa using key
  · simp only [ContinuousLinearMap.lsmul_apply]
    refine Continuous.integrable_of_hasCompactSupport ?_ hcs.smul_left
    exact Continuous.smul (by fun_prop) hc.continuous
  · simp only [ContinuousLinearMap.lsmul_apply]
    refine Continuous.integrable_of_hasCompactSupport (hoc.smul hc') (hcs.fderiv_apply ℝ v).smul_left
  · simp only [ContinuousLinearMap.lsmul_apply]
    exact Continuous.integrable_of_hasCompactSupport (hoc.smul hc.continuous) hcs.smul_left
  · intro x _
    have h := (B_hasFDerivAt_osc τ ((hφ.differentiable (by norm_num)) x)).hasLineDerivAt v
    convert h using 1
    simp [mul_assoc]
  · intro x _
    exact ((hc.differentiable (by norm_num)) x).hasFDerivAt.hasLineDerivAt v
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
