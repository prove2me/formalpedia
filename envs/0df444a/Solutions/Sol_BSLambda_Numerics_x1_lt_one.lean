-- Prove2me | solution 1 for BSLambda.Numerics.x1_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:49:27.134932+00:00
-- url     : https://prove2.me/submissions/92dce534-312e-47fd-a3b4-561f5fb98a12

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : x1 < 1 := by norm_num [x1]
end BSLambda.Numerics
