-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.rkF_eq_of_big_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:28.343457+00:00
-- url     : https://prove2.me/submissions/fa5bf73d-35e4-424d-97ff-2e97d5c95c3e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X)
variable {X F}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {g g' : Fin 2} {a a' : ZMod d} (h : X.big g a ↔ X.big g' a') : X.rkF g a = X.rkF g' a' := by
  unfold RowData.rkF
  by_cases hb : X.big g a
  · rw [X.rk_big g a hb, X.rk_big g' a' (h.1 hb)]
  · rw [X.rk_small g a hb, X.rk_small g' a' (fun h' => hb (h.2 h'))]
end Formalism.L2.FormalSeriesBounds.RF
