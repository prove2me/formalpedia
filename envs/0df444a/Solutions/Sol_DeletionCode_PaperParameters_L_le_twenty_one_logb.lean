-- Prove2me | solution 1 for DeletionCode.PaperParameters.L_le_twenty_one_logb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:47:41.561771+00:00
-- url     : https://prove2.me/submissions/b5d0db27-1418-4184-8ee8-76b9153a7877

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_L_eq
import Theorems.Thm_DeletionCode_PaperParameters_one_le_logb

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) :
    (L n : ℝ) ≤ 21 * Real.logb 2 (n : ℝ) := by
  have hlog := one_le_logb n hn
  have hceil : (Nat.clog 2 n : ℝ) < Real.logb 2 (n : ℝ) + 1 := by
    have he : Nat.clog 2 n = ⌈Real.logb 2 (n : ℝ)⌉₊ := by
      symm
      simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 n
    rw [he]
    exact Nat.ceil_lt_add_one (by linarith)
  have hL : (L n : ℝ) = 6 * (Nat.clog 2 n : ℝ) + 9 := by
    exact_mod_cast L_eq n
  linarith
end DeletionCode.PaperParameters
