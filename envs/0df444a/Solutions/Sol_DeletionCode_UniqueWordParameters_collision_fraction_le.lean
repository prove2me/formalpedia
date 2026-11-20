-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.collision_fraction_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:05.601009+00:00
-- url     : https://prove2.me/submissions/4f059fea-b173-44c2-bc32-3f4a7e17196d

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_UniqueWordParameters
import Theorems.Thm_DeletionCode_UniqueWordParameters_eight_mul_choose_le_pow

set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordParameters
namespace DeletionCode.UniqueWordParameters
theorem _root_.solution (n : ℕ) :
    (n.choose 2 : ℚ) / (2 : ℚ) ^ uniquenessLength n ≤ 1 / 8 := by
  have hpow : (0 : ℚ) < 2 ^ uniquenessLength n := pow_pos (by norm_num) _
  have hscaled : (8 : ℚ) * n.choose 2 ≤ (2 : ℚ) ^ uniquenessLength n := by
    exact_mod_cast eight_mul_choose_le_pow n
  apply (div_le_iff₀ hpow).mpr
  nlinarith
end DeletionCode.UniqueWordParameters
