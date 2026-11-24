-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.hs_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:21:26.140435+00:00
-- url     : https://prove2.me/submissions/e0b964a9-7081-4983-8f2d-887de6e7d094

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hsL_apply

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution (A B : Wq →L[ℂ] Wp) : ‖hsInner A B‖ ≤ hsK Wp Wq * (‖A‖ * ‖B‖) := by
  set L := (hsL : (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) with hL
  have hA : ‖hsVec A‖ ≤ ‖L‖ * ‖A‖ := by
    rw [← hsL_apply]
    exact L.le_opNorm A
  have hB : ‖hsVec B‖ ≤ ‖L‖ * ‖B‖ := by
    rw [← hsL_apply]
    exact L.le_opNorm B
  unfold hsInner hsK
  rw [← hL]
  calc ‖inner ℂ (hsVec B) (hsVec A)‖ ≤ ‖hsVec B‖ * ‖hsVec A‖ := norm_inner_le_norm _ _
    _ ≤ (‖L‖ * ‖B‖) * (‖L‖ * ‖A‖) := mul_le_mul hB hA (norm_nonneg _) (by positivity)
    _ = ‖L‖ ^ 2 * (‖A‖ * ‖B‖) := by ring
end Formalism.FourierDecayAlt.P.B5
