-- Prove2me | solution 1 for Freiman.other22_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:08:07.661676+00:00
-- url     : https://prove2.me/submissions/007c2262-9cbe-4f2f-add2-54812945a8c2

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_other22_record_exclusion
import Theorems.Thm_Freiman_other22_residual_capture

open Freiman

theorem solution (k : Fin 6) (hb : other22AllBindings) (hw : other22AllWitnesses)
    (r s q : ℝ) (hm : certRectangleMem (other22Paths k).rectangle r s)
    (hsource : ∃ bs ∈ lowerHistorySourcePremises (other22Paths k), lowerHistoryConditions bs r s q) :
    lowerHistoryComparisonsHold (other22Paths k) r s q := by
  classical
  obtain ⟨bs,hbs,hs⟩ := hsource
  obtain ⟨ai,hai⟩ := List.mem_iff_getElem?.mp hbs
  have hlen : ai < (lowerHistorySourcePremises (other22Paths k)).length := by
    exact (List.getElem?_eq_some_iff.mp hai).1
  intro z hz hc
  obtain ⟨bi,hbi⟩ := List.mem_iff_getElem?.mp hz
  obtain ⟨record,hr,hk,ha,hb'⟩ := (hb k).2 ai hlen bi z.1 z.2 hbi
  have binding := (hb k).1 record hr hk
  have valid := hw record.witness binding.1 binding.2.1
  by_contra hn
  have residual := other22_residual_capture (other22Paths k) ai bi bs z.1 z.2 hai hbi r s q hs hc hn
  have rect : certRectangleMem (other22Paths record.caseId).rectangle r s := by rw [hk]; exact hm
  apply other22_record_exclusion record binding valid r s q rect
  simpa only [hk,ha,hb'] using residual
