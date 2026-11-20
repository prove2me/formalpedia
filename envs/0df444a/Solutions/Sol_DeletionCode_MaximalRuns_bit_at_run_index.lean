-- Prove2me | solution 1 for DeletionCode.MaximalRuns.bit_at_run_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:20.133796+00:00
-- url     : https://prove2.me/submissions/7307bf4a-c8cb-4332-aeee-cd9bb83f5c90

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
import Theorems.Thm_DeletionCode_MaximalRuns_constantOn_block

set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (pre suffix : List Bool) (rho : ℕ) (bit : Bool) (pos : ℕ)
    (hstart : pre.length ≤ pos) (hstop : pos < pre.length + rho) :
    listLetters (pre ++ List.replicate rho bit ++ suffix) pos = bit := by
  have h := constantOn_block pre suffix rho bit (pos - pre.length) (by omega)
  have hindex : pre.length + (pos - pre.length) = pos := by omega
  simpa only [hindex] using h
end DeletionCode.MaximalRuns
