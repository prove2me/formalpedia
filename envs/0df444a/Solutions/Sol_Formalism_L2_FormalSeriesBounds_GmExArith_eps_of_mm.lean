-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.eps_of_mm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:40.256816+00:00
-- url     : https://prove2.me/submissions/de6b04ac-d096-4991-8e59-2b34af8dbad8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution {ι : Type} [Finite ι] (f : ι → C) (h : ∀ i, V.MM (f i)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ i, V.Ge ε (f i) := by
  have h1 : ∀ i, ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ V.Ge e (f i) := by
    intro i
    have hi := h i
    unfold VF.MM at hi
    induction hv : V.v (f i) using WithTop.recTopCoe with
    | top => exact ⟨1, one_pos, le_rfl, by unfold VF.Ge; rw [hv]; exact le_top⟩
    | coe r =>
      rw [hv] at hi
      have hr : 0 < r := by exact_mod_cast hi
      exact ⟨min r 1, lt_min hr one_pos, min_le_right _ _, by
        unfold VF.Ge; rw [hv]; exact_mod_cast min_le_left r 1⟩
  choose e he0 he1 heg using h1
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, le_rfl, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_min e
    exact ⟨e i0, he0 i0, he1 i0, fun i => (heg i).mono (hi0 i)⟩
end Formalism.L2.FormalSeriesBounds.GmExArith
