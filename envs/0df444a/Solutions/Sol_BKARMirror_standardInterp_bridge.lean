-- Prove2me | solution 1 for BKARMirror.standardInterp_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:00.636562+00:00
-- url     : https://prove2.me/submissions/1f762d46-8e0a-41cb-928a-57a615fde39d

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
import Theorems.Thm_BKARMirror_reachable_thresholdGraph_iff
import Theorems.Thm_BKAR_Forest_le_standardInterp_iff_thresholdConnected
import Theorems.Thm_BKAR_Forest_standardInterp_mem_Icc


set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKARMirror
theorem _root_.solution (J : ForestIndex V)
    (data : BKAR.AcyclicEdgeSetData J.edges)
    (u : {e : Edge V // e ∈ J.edges} → ℝ)
    (hu : ∀ e : {e : Edge V // e ∈ J.edges}, 0 ≤ u e ∧ u e ≤ 1) :
    standardInterp J u = (data.toForest).standardInterp u := by
  funext e
  have hu' : ∀ e : (data.toForest).EdgeParam, 0 ≤ u e ∧ u e ≤ 1 := hu
  have hr := (data.toForest).standardInterp_mem_Icc u hu' e
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ((thresholdGraph J u s).Reachable e.left e.right ↔
        s ≤ (data.toForest).standardInterp u e) := by
    intro s hs0 hs1
    rw [(data.toForest).le_standardInterp_iff_thresholdConnected u hs0 hs1 e]
    exact reachable_thresholdGraph_iff J data u s e
  show sSup {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧
      (thresholdGraph J u s).Reachable e.left e.right}
      = (data.toForest).standardInterp u e
  apply le_antisymm
  · apply Real.sSup_le
    · rintro s ⟨hs0, hs1, hreach⟩
      rcases eq_or_lt_of_le hs0 with h0 | h0
      · exact h0 ▸ hr.1
      · exact (key s h0 hs1).mp hreach
    · exact hr.1
  · rcases eq_or_lt_of_le hr.1 with h0 | h0
    · rw [← h0]
      apply Real.sSup_nonneg
      rintro s ⟨hs0, _, _⟩
      exact hs0
    · apply le_csSup
      · exact ⟨1, fun s hs => hs.2.1⟩
      · exact ⟨hr.1, hr.2, (key _ h0 hr.2).mpr le_rfl⟩
end BKARMirror
