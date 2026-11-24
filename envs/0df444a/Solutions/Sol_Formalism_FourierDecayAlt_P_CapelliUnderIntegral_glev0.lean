-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:15:44.715033+00:00
-- url     : https://prove2.me/submissions/bdd1282d-ecbb-451e-abfb-e1f6bba13eed

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliUnderIntegral
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.CapelliUnderIntegral
theorem _root_.solution {k r : ℕ} (g : Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ GV k r := by
  simp only [Q.Glev, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, fun a ha => by simp at ha⟩
end Formalism.FourierDecayAlt.P.CapelliUnderIntegral
