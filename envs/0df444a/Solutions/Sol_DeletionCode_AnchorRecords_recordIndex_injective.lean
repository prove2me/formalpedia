-- Prove2me | solution 1 for DeletionCode.AnchorRecords.recordIndex_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:01:28.222385+00:00
-- url     : https://prove2.me/submissions/9e8653eb-24de-4582-b0ca-3642f13a9721

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_recordRank_strict

set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (trace : Trace) : Function.Injective (recordIndex trace) := by
  intro c d heq
  have hv : recordRank trace c = recordRank trace d := congrArg Fin.val heq
  apply Subtype.ext
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := recordRank_strict trace c d hlt
    omega
  · have := recordRank_strict trace d c hgt
    omega
end DeletionCode.AnchorRecords
