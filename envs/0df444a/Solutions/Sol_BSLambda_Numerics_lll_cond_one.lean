-- Prove2me | solution 1 for BSLambda.Numerics.lll_cond_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:48.695326+00:00
-- url     : https://prove2.me/submissions/2049cc23-606c-418f-b8e6-248a1158b54b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Theorems.Thm_BSLambda_Numerics_x1_lt_one
public import Theorems.Thm_BSLambda_Numerics_x2_lt_one
public import Theorems.Thm_BSLambda_Numerics_loss_one_lt
public import Theorems.Thm_BSLambda_Numerics_add_mul_neg_log_one_sub_le
public import Theorems.Thm_BSLambda_Numerics_le_mul_pow_mul_pow_of_lt_log
public import Theorems.Thm_BSLambda_Numerics_log_29_div_16_gt


set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : p1 ≤ x1 * (1 - x1) ^ D11 * (1 - x2) ^ D12 := by
  nth_rewrite 1 [show x1 = 29 / 16 * p1 by norm_num [x1, p1]]
  exact le_mul_pow_mul_pow_of_lt_log (by norm_num [p1]) (by norm_num) (sub_pos.mpr x1_lt_one)
    (sub_pos.mpr x2_lt_one)
    ((add_mul_neg_log_one_sub_le D11 D12).trans_lt (loss_one_lt.trans log_29_div_16_gt))
end BSLambda.Numerics
