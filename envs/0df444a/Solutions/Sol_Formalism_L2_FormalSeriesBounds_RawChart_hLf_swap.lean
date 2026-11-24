-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.hLf_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:19.477746+00:00
-- url     : https://prove2.me/submissions/9d79be24-75e1-4dee-a00b-a01e6a90f208

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_onLf_swap
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
theorem _root_.solution (a a' : ZMod d) : X.hLf 1 a' a = X.hLf 0 a a' := by
  unfold hLf
  funext μ
  exact if_congr (by simp only [onLf_swap]) rfl rfl
end Formalism.L2.FormalSeriesBounds.RawChart
