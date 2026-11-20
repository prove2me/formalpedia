-- Prove2me | solution 1 for DeletionCode.OptimalRedundancy.optimalCodeSize_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:20:41.669596+00:00
-- url     : https://prove2.me/submissions/6b3ef453-e934-40e8-856f-a97261a9af79

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
import Theorems.Thm_DeletionCode_OptimalRedundancy_one_le_optimalCodeSize

set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter
namespace DeletionCode.OptimalRedundancy
theorem _root_.solution (t n : ℕ) : 0 < optimalCodeSize t n :=
  one_le_optimalCodeSize t n
end DeletionCode.OptimalRedundancy
