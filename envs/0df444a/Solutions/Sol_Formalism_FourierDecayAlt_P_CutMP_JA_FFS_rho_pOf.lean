-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rho_pOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:41.823904+00:00
-- url     : https://prove2.me/submissions/222503e7-fbc5-4c05-9015-316f47e55849

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableEquivOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
open Formalism.QuantumDeterminants.WeylGroupFacts
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
theorem _root_.solution (D : B.RealPlaceData k r Wp Wq) (a b c d : B.Mat k r) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.rho D (pOf a b c d) F = fun x => (D.π a).comp ((F (a⁻¹ * b⁻¹ * x * d * c)).comp (D.π' c⁻¹)) := by
  funext x
  simp [B.rho, B.sgs, pOf]
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
