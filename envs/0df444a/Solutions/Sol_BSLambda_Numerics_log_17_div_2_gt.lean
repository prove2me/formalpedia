-- Prove2me | solution 1 for BSLambda.Numerics.log_17_div_2_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:53.971829+00:00
-- url     : https://prove2.me/submissions/bfa0c38b-d49a-4a91-9360-59f418605fac

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Theorems.Thm_BSLambda_Numerics_log_17_div_16_gt

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : (2.138 : ℝ) < Real.log (17 / 2) := by
  rw [show (17 / 2 : ℝ) = 2 ^ (3 : ℕ) * (17 / 16) by norm_num,
    Real.log_mul (by positivity) (by norm_num), Real.log_pow, Nat.cast_ofNat]
  linarith [Real.log_two_gt_d9, log_17_div_16_gt]
end BSLambda.Numerics
