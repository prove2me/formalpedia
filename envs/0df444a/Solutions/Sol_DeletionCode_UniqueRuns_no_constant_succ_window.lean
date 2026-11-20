-- Prove2me | solution 1 for DeletionCode.UniqueRuns.no_constant_succ_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:09.190473+00:00
-- url     : https://prove2.me/submissions/52785297-2ff7-45ac-964d-235b5a00c6bd

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_UniqueRuns
import Theorems.Thm_DeletionCode_UniqueRuns_constant_length_le

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueRuns
open Windows
namespace DeletionCode.UniqueRuns
theorem _root_.solution (k n : ℕ) (x : Letters) (hx : KUnique x n k)
    (a : ℕ) (bit : Bool) (hbound : a + (k + 1) ≤ n) :
    ¬ ConstantOn x a (k + 1) bit := by
  intro hconstant
  have h := constant_length_le k n x hx a (k + 1) bit hbound hconstant
  omega
end DeletionCode.UniqueRuns
