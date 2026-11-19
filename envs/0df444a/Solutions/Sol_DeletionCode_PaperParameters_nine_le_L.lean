-- Prove2me | solution 1 for DeletionCode.PaperParameters.nine_le_L
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:36:47.0962+00:00
-- url     : https://prove2.me/submissions/1264f8e0-57d4-41f2-8f62-23a71284e54f

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_L_eq

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (n : ℕ) : 9 ≤ L n := by rw [L_eq]; omega
end DeletionCode.PaperParameters
