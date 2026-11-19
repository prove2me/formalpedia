-- Prove2me | solution 1 for DeletionCode.MaximalRuns.eraseIdx_in_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:23:38.481414+00:00
-- url     : https://prove2.me/submissions/3a7d945c-7869-406e-94cb-27297acee510

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns

set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (pre suffix : List Bool) (rho : ℕ) (bit : Bool) (pos : ℕ)
    (hstart : pre.length ≤ pos) (hstop : pos < pre.length + rho) :
    (pre ++ List.replicate rho bit ++ suffix).eraseIdx pos =
      pre ++ List.replicate (rho - 1) bit ++ suffix := by
  simp only [List.append_assoc]
  have hrun : pos - pre.length < rho := by omega
  rw [List.eraseIdx_append_of_length_le hstart]
  rw [List.eraseIdx_append_of_lt_length
    (by simpa only [List.length_replicate] using hrun)]
  rw [List.eraseIdx_replicate, if_pos hrun]
end DeletionCode.MaximalRuns
