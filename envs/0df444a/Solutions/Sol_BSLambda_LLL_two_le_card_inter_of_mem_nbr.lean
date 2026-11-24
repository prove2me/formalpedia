-- Prove2me | solution 1 for BSLambda.LLL.two_le_card_inter_of_mem_nbr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:25:52.720191+00:00
-- url     : https://prove2.me/submissions/9162c044-17f2-4017-8616-028baef615cb

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_disjoint_offDiag_of_card_inter_le_one
public import Theorems.Thm_BSLambda_LLL_mem_nbr
attribute [local simp] BSLambda.LLL.mem_nbr



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution {i j : BadIdx Arc}
    (h : j ∈ nbr (badSupp (Arc := Arc)) i) :
    2 ≤ (badVerts i ∩ badVerts j).card :=
  Nat.lt_of_not_le fun hle ↦ (mem_nbr.mp h).2 (disjoint_offDiag_of_card_inter_le_one hle)
end BSLambda.LLL
