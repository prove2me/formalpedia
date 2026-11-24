-- Prove2me | solution 1 for BSLambda.Numerics.log_17_div_16_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:17.279811+00:00
-- url     : https://prove2.me/submissions/85e52ffc-663c-43bf-b37f-591a3a15f929

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : (1 / 17 : ℝ) < Real.log (17 / 16) := by
  have hinv : Real.log (17 / 16 : ℝ) = -Real.log (16 / 17) := by norm_num [← Real.log_inv]
  linarith [Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 16 / 17 by norm_num) (by norm_num)]
end BSLambda.Numerics
