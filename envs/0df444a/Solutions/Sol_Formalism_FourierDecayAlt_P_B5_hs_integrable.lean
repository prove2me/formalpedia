-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.hs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:56:38.710099+00:00
-- url     : https://prove2.me/submissions/9e8563de-6832-4e6f-bd28-4134452bed28

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hs_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_aesm_of_continuousOn

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {A B : Mat k r → (Wq →L[ℂ] Wp)}
    (hA : ContinuousOn A (GV k r)) (hB : ContinuousOn B (GV k r))
    (h : Integrable (fun g : Mt k r => ‖B (Matrix.of g)‖ * ‖A (Matrix.of g)‖) D.μG) :
    Integrable (fun g : Mt k r => hsInner (A (Matrix.of g)) (B (Matrix.of g))) D.μG := by
  have hc : ContinuousOn (fun x => hsInner (A x) (B x)) (GV k r) :=
    hs_continuous.comp_continuousOn (hA.prodMk hB)
  refine (h.const_mul (hsK Wp Wq)).mono' (aesm_of_continuousOn D.haarG hc) (ae_of_all _ fun g => ?_)
  calc ‖hsInner (A (Matrix.of g)) (B (Matrix.of g))‖
      ≤ hsK Wp Wq * (‖A (Matrix.of g)‖ * ‖B (Matrix.of g)‖) := hs_norm_le _ _
    _ = hsK Wp Wq * (‖B (Matrix.of g)‖ * ‖A (Matrix.of g)‖) := by ring
end Formalism.FourierDecayAlt.P.B5
