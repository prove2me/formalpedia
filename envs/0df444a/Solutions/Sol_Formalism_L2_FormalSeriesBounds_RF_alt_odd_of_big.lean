-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.alt_odd_of_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:33.725029+00:00
-- url     : https://prove2.me/submissions/e397e0c5-16b7-4233-81ef-3d8873883dbf

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_odd_sub_val
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_big_one_iff
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
theorem _root_.solution (hdich : X.Alt ∨ ∀ a, X.big 0 a) {g : Fin 2} {a a' : ZMod d} (h1 : X.big g a)
    (h2 : X.big (1 - g) a') : X.Alt ∧ Odd (a' - a).val := by
  have h3 : ¬ X.big g a' := (X.big_compl g a').1 h2
  rcases hdich with hA | hB
  · refine ⟨hA, odd_sub_val hA.1 a a' ?_⟩
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · rw [← hA.2 a, ← hA.2 a']
      tauto
    · rw [big_one_iff] at h1 h3
      rw [← hA.2 a, ← hA.2 a']
      tauto
  · exfalso
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · exact h3 (hB a')
    · rw [big_one_iff] at h1
      exact h1 (hB a)
end Formalism.L2.FormalSeriesBounds.RF
