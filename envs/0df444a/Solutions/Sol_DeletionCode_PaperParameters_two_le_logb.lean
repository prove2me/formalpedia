-- Prove2me | solution 1 for DeletionCode.PaperParameters.two_le_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:46:38.86995+00:00
-- url     : https://prove2.me/submissions/f5b77745-ced3-4394-b3a3-274d044c90f4

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) : 2 ≤ Real.logb 2 (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 2 ^ (2 : ℕ))
    (show (2 : ℝ) ^ (2 : ℕ) ≤ n by norm_num; exact_mod_cast hn)
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    Nat.cast_ofNat, mul_one] using h
end DeletionCode.PaperParameters
