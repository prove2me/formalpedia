-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.conj_inverse_map_has_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:10:08.039714+00:00
-- url     : https://prove2.me/submissions/05580258-265d-46d3-bc1d-e952f7c3e5d4

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
theorem _root_.solution (l c : ℂ) (hc : c ≠ 0) : HasFDerivAt (fun c : ℂ => l / conj c) (mi2D l c) c := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  have h1 : HasDerivAt (fun z : ℂ => l * z⁻¹) (l * -((conj c) ^ 2)⁻¹) (conj c) := (hasDerivAt_inv hc').const_mul l
  have h2 : HasFDerivAt (fun z : ℂ => l * z⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (l * -((conj c) ^ 2)⁻¹)).restrictScalars ℝ) (conj c) :=
    h1.hasFDerivAt.restrictScalars ℝ
  have h3 : HasFDerivAt (fun c : ℂ => conj c) (Complex.conjCLE : ℂ →L[ℝ] ℂ) c := Complex.conjCLE.hasFDerivAt
  have h4 := HasFDerivAt.comp c h2 h3
  have he : (fun c : ℂ => l / conj c) = (fun z : ℂ => l * z⁻¹) ∘ (fun c : ℂ => conj c) := by
    funext z; simp [div_eq_mul_inv]
  rw [he]; exact h4
end Formalism.FourierDecayAlt.P.B2x8
