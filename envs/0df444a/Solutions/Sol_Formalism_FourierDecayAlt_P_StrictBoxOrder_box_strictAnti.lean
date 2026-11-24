-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StrictBoxOrder.box_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:56:38.806957+00:00
-- url     : https://prove2.me/submissions/a42bae98-f717-4a02-8029-ab488b9b9294

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StrictBoxOrder
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.StrictBoxOrder
theorem _root_.solution {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) : StrictAnti M := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ k =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have h1 := (h i.succ).2
    have h2 := (h i.castSucc).1
    rw [Fin.succ_castSucc] at h2
    exact lt_of_le_of_lt h1 h2
end Formalism.FourierDecayAlt.P.StrictBoxOrder
