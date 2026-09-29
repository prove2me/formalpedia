-- Prove2me | solution 1 for Freiman.lowerHistory_path_soundness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:15.520776+00:00
-- url     : https://prove2.me/submissions/084495ad-8c9e-41f5-9e67-d5bf1d1adba2

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_path_logic
import Theorems.Thm_Freiman_lowerHistory_record_exclusion
import Theorems.Thm_Freiman_lowerHistory_complement

open Freiman

theorem solution (p : LowerHistoryPath) (hp : p ∈ lowerHistoryPaths.toList)
    (hb : lowerHistoryAllBindings) (hw : lowerHistoryAllWitnesses)
    (r s q : ℝ) (hm : certRectangleMem p.rectangle r s)
    (hsource : ∃ bs ∈ lowerHistorySourcePremises p, lowerHistoryConditions bs r s q) :
    (p.catalog = .initial ∧ lowerHistorySurvivor p) ∨
      (p.catalog ≠ .initial ∧ p.row ≠ 4 ∧ lowerHistoryComparisonsHold p r s q) := by
  have hbind := hb p hp
  apply lowerHistory_path_logic lowerHistory_complement p hbind r s q hsource
  intro record hrec hs
  have hr := hbind.2.1 record hrec
  have hd := hr
  simp only [lowerHistoryRecordBinding, hs, Bool.false_eq_true, ↓reduceIte] at hd
  exact lowerHistory_record_exclusion p record hr hs (hw _ hd.2.2.1 hd.2.2.2.1) r s q hm
