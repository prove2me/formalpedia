-- Prove2me | solution 1 for BSLambda.LLL.badX_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:37.75536+00:00
-- url     : https://prove2.me/submissions/8970392f-be60-41f4-9e82-5a3d8490e19f

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_Numerics_x1_lt_one
public import Theorems.Thm_BSLambda_Numerics_x2_lt_one


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (t : Bool) : badX t < 1 := by
  cases t with
  | false => exact x1_lt_one
  | true => exact x2_lt_one
end BSLambda.LLL
