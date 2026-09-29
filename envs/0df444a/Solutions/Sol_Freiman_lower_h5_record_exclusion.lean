-- Prove2me | solution 1 for Freiman.lower_h5_record_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:42.238301+00:00
-- url     : https://prove2.me/submissions/b46b83ad-dea4-4c63-9f01-d86106354e9f

import Theorems.Thm_Freiman_cert_witness_excludes
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
theorem solution (c : LowerH5Case) (record : LowerH5Record) (hb : LowerH5RecordBinding c record)
    (hw : certWitnessValid (lowerH5Witness record.witness)) (r s q : ℝ)
    (hr : certRectangleMem c.rectangle r s) (hs : lowerHistoryConditions (lowerH5RecordBounds record) r s q) : False := by
  apply cert_witness_excludes (lowerH5Witness record.witness) hw r s q
  · simpa only [hb.rectangle] using hr
  · exact ⟨hs _ hb.lowerMember,hs _ hb.upperMember⟩
