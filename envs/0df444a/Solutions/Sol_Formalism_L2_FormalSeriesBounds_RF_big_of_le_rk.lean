-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.big_of_le_rk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:30.970452+00:00
-- url     : https://prove2.me/submissions/bdf03458-7b53-4480-ba4f-2d36304fa140

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
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (hj : X.j' < X.n) {g : Fin 2} {a : ZMod d} (h : X.n ≤ X.rkF g a) : X.big g a := by
  by_contra hb
  have := X.rk_small g a hb
  unfold RowData.rkF at h
  omega
end Formalism.L2.FormalSeriesBounds.RF
