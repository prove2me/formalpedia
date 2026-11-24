-- Prove2me | solution 1 for BSLambda.LLL.headOut_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:00:02.117447+00:00
-- url     : https://prove2.me/submissions/7f8b38e0-ced7-4e4e-88cb-74d15e1e3345

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (o : ι) : headOut Arc (o, none) = outNbrs Arc o := rfl
end BSLambda.LLL
