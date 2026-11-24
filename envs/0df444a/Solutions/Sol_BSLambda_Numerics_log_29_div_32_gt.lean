-- Prove2me | solution 1 for BSLambda.Numerics.log_29_div_32_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:16.811057+00:00
-- url     : https://prove2.me/submissions/102cbe72-d01a-4391-9e5c-7480339a0c75

module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : (-0.0986 : ℝ) < Real.log (29 / 32) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(3 / 32 : ℝ)| < 1 by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith [(abs_le.mp h).1]
end BSLambda.Numerics
