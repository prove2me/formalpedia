-- Prove2me | solution 1 for BSLambda.Numerics.loss_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:51.574659+00:00
-- url     : https://prove2.me/submissions/60dc56aa-b44c-4a4e-9fc1-2f46ccd45249

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : (D11 : ℝ) * (x1 / (1 - x1)) + (D12 : ℝ) * (x2 / (1 - x2)) < 0.594 := by
  norm_num [D11, D12, x1, x2]
end BSLambda.Numerics
