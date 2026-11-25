-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.le_sum_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:49.359803+00:00
-- url     : https://prove2.me/submissions/a8ba5658-ef45-4608-bd88-14956c736f42

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
theorem _root_.solution {α : Type} (l : List α) (f : α → ℕ) {q : α} (hq : q ∈ l) : f q ≤ (l.map f).sum := by
  induction l with
  | nil => exact absurd hq (by simp)
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hq with rfl | h
    · omega
    · have := ih h
      omega
end Formalism.L2.FormalSeriesBounds.RF
