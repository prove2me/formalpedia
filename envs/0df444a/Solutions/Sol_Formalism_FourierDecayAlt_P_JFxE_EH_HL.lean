-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.EH_HL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:42.505925+00:00
-- url     : https://prove2.me/submissions/31b291e4-d8e4-4f75-ae5c-b952e040a3b1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution : HL (Q.EH (E := E) k r) := by
  intro a b f f₂ h
  exact EH_congr a b f f₂ h
end Formalism.FourierDecayAlt.P.JFxE
