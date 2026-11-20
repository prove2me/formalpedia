-- Prove2me | solution 1 for DeletionCode.UniqueWordParameters.collision_fraction_le_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:06.201018+00:00
-- url     : https://prove2.me/submissions/fb6d93f4-63e6-4d06-acdc-7a2c5f894d7a

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
    (n.choose 2 : ℝ) / (2 : ℝ) ^ uniquenessLength n ≤ 1 / 8 := by
  have hpow : (0 : ℝ) < 2 ^ uniquenessLength n := pow_pos (by norm_num) _
  have hscaled : (8 : ℝ) * n.choose 2 ≤ (2 : ℝ) ^ uniquenessLength n := by
    exact_mod_cast eight_mul_choose_le_pow n
  apply (div_le_iff₀ hpow).mpr
  nlinarith
end DeletionCode.UniqueWordParameters
