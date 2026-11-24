-- Prove2me | solution 1 for BSLambda.Numerics.log_29_div_16_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:53.206359+00:00
-- url     : https://prove2.me/submissions/2334fb63-5c97-4319-8492-1c094fe60409

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Theorems.Thm_BSLambda_Numerics_log_29_div_32_gt

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : (0.594 : ℝ) < Real.log (29 / 16) := by
  rw [show (29 / 16 : ℝ) = 2 * (29 / 32) by norm_num, Real.log_mul two_ne_zero (by norm_num)]
  linarith [Real.log_two_gt_d9, log_29_div_32_gt]
end BSLambda.Numerics
