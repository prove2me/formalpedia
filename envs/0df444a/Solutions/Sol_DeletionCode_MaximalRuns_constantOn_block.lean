-- Prove2me | solution 1 for DeletionCode.MaximalRuns.constantOn_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:21:59.93119+00:00
-- url     : https://prove2.me/submissions/d03449f9-b573-4d1c-a99e-6f1168b7db0d

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns

set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (pre suffix : List Bool) (rho : ℕ) (bit : Bool) :
    ConstantOn (listLetters (pre ++ List.replicate rho bit ++ suffix)) pre.length rho bit := by
  intro i hi
  simp only [List.append_assoc]
  simp only [listLetters, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  have hindex : pre.length + i - pre.length = i := by omega
  rw [hindex]
  rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hi)]
  rw [List.getElem?_replicate_of_lt hi]
  rfl
end DeletionCode.MaximalRuns
