-- Prove2me | solution 1 for BSLambda.LLL.card_nbr_type_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:15.716892+00:00
-- url     : https://prove2.me/submissions/d1f0126c-26d8-4cd4-b6ac-a0ead495c529

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_badVerts_mem_filter_of_mem_nbr
public import Theorems.Thm_BSLambda_LLL_badVerts_injOn_type_two

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (i : BadIdx Arc) :
    ((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = true).card
      ≤ (Finset.univ.filter fun S : Finset ι =>
          S.card = 9 ∧ 2 ≤ (badVerts i ∩ S).card).card :=
  Finset.card_le_card_of_injOn badVerts (fun _ hj ↦ badVerts_mem_filter_of_mem_nbr hj)
    (badVerts_injOn_type_two i)
end BSLambda.LLL
