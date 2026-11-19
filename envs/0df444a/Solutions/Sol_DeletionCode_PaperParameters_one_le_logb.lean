-- Prove2me | solution 1 for DeletionCode.PaperParameters.one_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:46:36.477219+00:00
-- url     : https://prove2.me/submissions/fd218cfa-2817-416f-a319-c45d0764022a

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Real.logb 2 (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ n by exact_mod_cast hn)
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
end DeletionCode.PaperParameters
