-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StrictBoxOrder.pow_pres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:56:35.410272+00:00
-- url     : https://prove2.me/submissions/fe87fc43-80fd-4d1b-bcea-e8613f233705

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
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
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.StrictBoxOrder
theorem _root_.solution (P : V → Prop) (f : Module.End ℂ V) (h : ∀ v, P v → P (f v)) (k : ℕ) :
    ∀ v, P v → P ((f ^ k) v) := by
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
    intro v hv
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (h v hv)
end Formalism.FourierDecayAlt.P.StrictBoxOrder
