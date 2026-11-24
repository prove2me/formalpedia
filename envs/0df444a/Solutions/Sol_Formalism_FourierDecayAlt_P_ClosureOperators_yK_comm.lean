-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.yK_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:57:55.322243+00:00
-- url     : https://prove2.me/submissions/0b3d573e-bf20-4428-9795-0a2e3cd18125

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution {n : ℕ} {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    yK E a * yK E b = yK E b * yK E a := by
  have h := hE (Fin.last n) a.castSucc (Fin.last n) b.castSucc
  rw [if_neg (Fin.castSucc_lt_last a).ne, if_neg (Fin.castSucc_lt_last b).ne, sub_zero] at h
  exact sub_eq_zero.mp h
end Formalism.FourierDecayAlt.P.ClosureOperators
