-- Prove2me | solution 1 for BSLambda.Numerics.add_mul_neg_log_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:47.311344+00:00
-- url     : https://prove2.me/submissions/ed31000f-4e0e-425b-89f4-12c2324369a7

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Theorems.Thm_BSLambda_Numerics_x1_lt_one
public import Theorems.Thm_BSLambda_Numerics_x2_lt_one
public import Theorems.Thm_BSLambda_Numerics_neg_log_one_sub_le


set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution (m n : ℕ) :
    (m : ℝ) * -Real.log (1 - x1) + (n : ℝ) * -Real.log (1 - x2) ≤
      (m : ℝ) * (x1 / (1 - x1)) + (n : ℝ) * (x2 / (1 - x2)) := by
  gcongr
  · exact neg_log_one_sub_le x1_lt_one
  · exact neg_log_one_sub_le x2_lt_one
end BSLambda.Numerics
