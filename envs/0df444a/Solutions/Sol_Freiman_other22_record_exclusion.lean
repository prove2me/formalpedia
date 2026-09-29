-- Prove2me | solution 1 for Freiman.other22_record_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:08:07.81285+00:00
-- url     : https://prove2.me/submissions/6d004413-9895-49b5-8788-c32d6221e13c

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_cert_witness_excludes

open Freiman

theorem solution (record : Other22Record) (hb : other22RecordBinding record)
    (hw : certWitnessValid (other22Witness record.witness))
    (r s q : ℝ) (hm : certRectangleMem (other22Paths record.caseId).rectangle r s) :
    ¬ lowerHistoryConditions (lowerHistoryResidual (other22Paths record.caseId) record.alternative (record.branch : ℤ)) r s q := by
  intro hs
  rcases hb with ⟨_,_,he,hl,hu,hr⟩
  have transfer : ∀ b ∈ other22RecordPremise record,
      b ∈ lowerHistoryResidual (other22Paths record.caseId) record.alternative (record.branch : ℤ) := by
    intro b hm
    apply List.mem_toFinset.mp
    rw [← he]
    exact List.mem_toFinset.mpr hm
  have hm' : certRectangleMem (other22Witness record.witness).rectangle r s := by rw [hr]; exact hm
  exact cert_witness_excludes _ hw r s q hm'
    ⟨hs _ (transfer _ hl),hs _ (transfer _ hu)⟩
