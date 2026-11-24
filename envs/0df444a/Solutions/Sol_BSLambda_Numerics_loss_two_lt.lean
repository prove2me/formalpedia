-- Prove2me | solution 1 for BSLambda.Numerics.loss_two_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:54.011743+00:00
-- url     : https://prove2.me/submissions/d0757932-2267-4331-8f41-8e8ba8020965

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : (D21 : ℝ) * (x1 / (1 - x1)) + (D22 : ℝ) * (x2 / (1 - x2)) < 2.138 := by
  norm_num [D21, D22, x1, x2]
end BSLambda.Numerics
