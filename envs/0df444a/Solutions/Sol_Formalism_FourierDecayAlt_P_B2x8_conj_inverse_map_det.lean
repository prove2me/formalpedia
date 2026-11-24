-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.conj_inverse_map_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:10:04.821552+00:00
-- url     : https://prove2.me/submissions/27aa902d-78e2-4ea9-877f-dda36f74e186

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (l c : ℂ) : (mi2D l c).det = -(‖l‖ ^ 2 * (‖c‖ ^ 4)⁻¹) := by
  unfold mi2D ContinuousLinearMap.det
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars]
  have h1 : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (l * -((conj c) ^ 2)⁻¹) : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ) =
      (l * -((conj c) ^ 2)⁻¹) • LinearMap.id := by
    ext; simp
  have h2 : LinearMap.det ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = -1 := Complex.det_conjAe
  rw [h1, h2, LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]
  simp only [norm_mul, norm_neg, norm_inv, norm_pow, RCLike.norm_conj]
  ring
end Formalism.FourierDecayAlt.P.B2x8
