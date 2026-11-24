-- Prove2me | solution 1 for BSLambda.Numerics.lll_cond_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:30.999094+00:00
-- url     : https://prove2.me/submissions/01c084db-a1be-4e25-a748-cc3e717eb673

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Theorems.Thm_BSLambda_Numerics_x1_lt_one
public import Theorems.Thm_BSLambda_Numerics_x2_lt_one
public import Theorems.Thm_BSLambda_Numerics_loss_two_lt
public import Theorems.Thm_BSLambda_Numerics_add_mul_neg_log_one_sub_le
public import Theorems.Thm_BSLambda_Numerics_le_mul_pow_mul_pow_of_lt_log
public import Theorems.Thm_BSLambda_Numerics_log_17_div_2_gt


set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : p2 ≤ x2 * (1 - x1) ^ D21 * (1 - x2) ^ D22 := by
  nth_rewrite 1 [show x2 = 17 / 2 * p2 by norm_num [x2, p2]]
  exact le_mul_pow_mul_pow_of_lt_log (by norm_num [p2]) (by norm_num) (sub_pos.mpr x1_lt_one)
    (sub_pos.mpr x2_lt_one)
    ((add_mul_neg_log_one_sub_le D21 D22).trans_lt (loss_two_lt.trans log_17_div_2_gt))
end BSLambda.Numerics
