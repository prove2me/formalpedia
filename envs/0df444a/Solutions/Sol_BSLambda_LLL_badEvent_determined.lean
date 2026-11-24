-- Prove2me | solution 1 for BSLambda.LLL.badEvent_determined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:57.52067+00:00
-- url     : https://prove2.me/submissions/bebb6278-820e-4142-a01b-9f949c69722f

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_flagEvent_determined
public import Theorems.Thm_BSLambda_LLL_radiusTwoEvent_determined


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (hT : IsTournament Arc) (i : BadIdx Arc) :
    Determined (β := fun _ : ι × ι => Fin r) (badSupp i) (badEvent (r := r) Arc i) := by
  cases i with
  | inl F => exact flagEvent_determined hT F.2
  | inr S => exact radiusTwoEvent_determined hT S.1
end BSLambda.LLL
