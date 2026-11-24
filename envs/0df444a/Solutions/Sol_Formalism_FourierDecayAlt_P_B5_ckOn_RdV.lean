-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.ckOn_RdV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:21:16.259862+00:00
-- url     : https://prove2.me/submissions/ae4c0159-2ab9-4cf3-a74d-460bd8cdd494

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hasDerivAt_of_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution {m : ℕ∞} {f : Mat k r → E} {X : Mat k r} (hX : inLie k r X) (h : CkOn (m + 1) (GV k r) f) :
    CkOn m (GV k r) (RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  refine ⟨U, fun g => fderiv ℝ f' g (g * X), hU, hgU, ?_, ?_⟩
  · have h2 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun g : Mat k r => g * X) U :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff.contDiffOn
    exact (hf'.fderiv_of_isOpen hU (m := (m : WithTop ℕ∞)) (le_of_eq (by norm_cast))).clm_apply h2
  · intro g hg hgG
    have hd : DifferentiableAt ℝ f' g :=
      (hf'.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
    exact (hasDerivAt_of_ext hU hg hgG hX hd he).deriv
end Formalism.FourierDecayAlt.P.B5
