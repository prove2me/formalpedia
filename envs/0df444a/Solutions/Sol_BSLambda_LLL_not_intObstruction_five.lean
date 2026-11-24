-- Prove2me | solution 1 for BSLambda.LLL.not_intObstruction_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:40.256474+00:00
-- url     : https://prove2.me/submissions/3accc3ee-25e7-46fb-a37d-78a836e36b91

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_mem_flagEvent_of_intObstruction


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 5)
    {h : ι} (hh : h ∈ S) (hobs : IntObstruction Arc 1 S h (toGamma ω)) : False := by
  obtain ⟨F, hact, _, hmem⟩ := mem_flagEvent_of_intObstruction hT hS hh hobs
  exact hgood (Sum.inl ⟨F, hact⟩) hmem
end BSLambda.LLL
