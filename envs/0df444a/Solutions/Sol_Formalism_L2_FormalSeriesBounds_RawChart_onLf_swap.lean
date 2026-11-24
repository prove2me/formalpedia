-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.onLf_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:43.791727+00:00
-- url     : https://prove2.me/submissions/af8b3c48-efe0-40a8-95e5-9a7935e8ed81

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
variable {X}
variable (X)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (a a' : ZMod d) (w : WV I) : X.OnLf 1 a' a w ↔ X.OnLf 0 a a' w := by
  unfold OnLf
  simp only [sub_self, sub_zero]
  exact or_comm
end Formalism.L2.FormalSeriesBounds.RawChart
