-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.same_sign_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:21:26.433991+00:00
-- url     : https://prove2.me/submissions/69849fa0-4dc1-448f-89a5-0c60f3e36356

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
variable {S : Type}
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
theorem _root_.solution {a b : ℝ} (ha : 2 < |a|) (hb : 2 < |b|) (hab : b = a + 1 ∨ b = a - 1) :
    0 < a / b := by
  rcases lt_abs.1 ha with ha' | ha' <;> rcases hab with rfl | rfl
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
end Formalism.FourierDecayAlt.P.RealWeightedForms
