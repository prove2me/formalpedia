-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StrictBoxOrder.list_prod_pres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:56:34.596495+00:00
-- url     : https://prove2.me/submissions/52328168-f4a2-48e6-b2dc-69abc5b17492

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder

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
theorem _root_.solution (P : V → Prop) (l : List (Module.End ℂ V)) (h : ∀ f ∈ l, ∀ v, P v → P (f v)) :
    ∀ v, P v → P (l.prod v) := by
  induction l with
  | nil => intro v hv; simpa using hv
  | cons f l ih =>
    intro v hv
    rw [List.prod_cons, Module.End.mul_apply]
    exact h f (by simp) _ (ih (fun g hg => h g (by simp [hg])) v hv)
end Formalism.FourierDecayAlt.P.StrictBoxOrder
