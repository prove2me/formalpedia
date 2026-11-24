-- Prove2me | solution 1 for BSLambda.LLL.badP_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:33:06.210374+00:00
-- url     : https://prove2.me/submissions/00e3cd65-7c30-4d5f-83eb-255ef794f104

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_Numerics_lll_cond_one
public import Theorems.Thm_BSLambda_Numerics_lll_cond_two


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (t : Bool) :
    badP t ≤ badX t * (1 - badX false) ^ badD t false * (1 - badX true) ^ badD t true := by
  cases t with
  | false => exact lll_cond_one
  | true => exact lll_cond_two
end BSLambda.LLL
