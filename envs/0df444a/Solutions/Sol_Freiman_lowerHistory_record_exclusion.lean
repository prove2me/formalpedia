-- Prove2me | solution 1 for Freiman.lowerHistory_record_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:02.977162+00:00
-- url     : https://prove2.me/submissions/81e32950-930f-40b7-ac0c-2b136a70335c

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_cert_witness_excludes

open Freiman

theorem solution (p : LowerHistoryPath) (record : LowerHistoryRecord)
    (hb : lowerHistoryRecordBinding p record) (hs : record.survivor = false)
    (hw : certWitnessValid (lowerHistoryWitness record.witnessId))
    (r s q : ℝ) (hm : certRectangleMem p.rectangle r s) :
    ¬ lowerHistoryConditions (lowerHistoryResidual p record.alternative record.endpointBranch) r s q := by
  intro hc
  have hbind := hb
  simp only [lowerHistoryRecordBinding, hs, Bool.false_eq_true, ↓reduceIte] at hbind
  generalize hew : lowerHistoryWitness record.witnessId = w at hw hbind
  rcases hbind with ⟨_,_,_,_,heq,hl,hu,hr⟩
  have ht : lowerHistoryConditions (lowerHistoryPremise record.premiseId) r s q := by
    intro b hmem
    apply hc b
    have : b ∈ (lowerHistoryResidual p record.alternative record.endpointBranch).toFinset := by
      rw [← heq]
      exact List.mem_toFinset.mpr hmem
    exact List.mem_toFinset.mp this
  apply cert_witness_excludes w hw r s q
    (by simpa [hr] using hm)
  exact ⟨ht w.lowerBound hl, ht w.upperBound hu⟩
