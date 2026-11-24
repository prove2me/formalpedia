-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.dLR_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:16.252287+00:00
-- url     : https://prove2.me/submissions/0428806e-1b2c-4ed1-bb74-ec1efce4b6b6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u v : List (Mat k r)) :
    dLR u v (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
  have hR : ∀ w : List (Mat k r), Rw w (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
    intro w
    induction w with
    | nil => rfl
    | cons X w ih =>
      show RdV X (Rw w _) = _
      rw [ih]
      funext g
      simp only [RdV, deriv_const']
  induction u with
  | nil => exact hR v
  | cons X u ih =>
    show LdV X (dLR u v _) = _
    rw [ih]
    funext g
    simp only [LdV, deriv_const']
end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
