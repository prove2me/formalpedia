-- Prove2me | solution 1 for DeletionCode.OptimalRedundancy.card_le_optimalCodeSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:15:52.593024+00:00
-- url     : https://prove2.me/submissions/fd4d8173-a0b2-4589-807a-572622dececb

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
import Theorems.Thm_DeletionCode_OptimalRedundancy_mem_correctingCodes

set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter
namespace DeletionCode.OptimalRedundancy
theorem _root_.solution (t n : ℕ) (C : Finset (Bits n))
    (hC : CodeSelection.Corrects t C) : C.card ≤ optimalCodeSize t n := by
  unfold optimalCodeSize
  exact Finset.le_sup ((mem_correctingCodes t n C).mpr hC)
end DeletionCode.OptimalRedundancy
