-- Prove2me | solution 1 for BSLambda.LLL.not_intObstruction_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:22.95365+00:00
-- url     : https://prove2.me/submissions/c84b884d-8ad5-4dec-83bb-37b2fc6a2f69

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_mem_radiusTwoEvent


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) {S : Finset ι} (hS : S.card = 9)
    {h : ι} (hh : h ∈ S) (hobs : IntObstruction Arc 2 S h (toGamma ω)) : False := by
  have hev : ω ∈ radiusTwoEvent Arc S := mem_radiusTwoEvent.mpr ⟨h, hh, hobs⟩
  exact hgood (Sum.inr ⟨S, hS⟩) hev
end BSLambda.LLL
