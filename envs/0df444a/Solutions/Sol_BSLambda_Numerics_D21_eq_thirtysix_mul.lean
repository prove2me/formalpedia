-- Prove2me | solution 1 for BSLambda.Numerics.D21_eq_thirtysix_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:27.780629+00:00
-- url     : https://prove2.me/submissions/0408d1f5-f657-405a-9fee-340a59a6331c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Logs
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.Numerics
namespace BSLambda.Numerics
theorem _root_.solution : D21 = 36 * 214620087510 := by norm_num [D21]
end BSLambda.Numerics
