-- Prove2me | solution 1 for BSLambda.LLL.badVerts_mem_filter_of_mem_nbr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:29.653343+00:00
-- url     : https://prove2.me/submissions/29e4ced8-6c76-4353-bda9-603a2659971b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_exists_inr_of_badTy_eq_true
public import Theorems.Thm_BSLambda_LLL_two_le_card_inter_of_mem_nbr

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
    (hj : j ∈ (nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = true) :
    badVerts j ∈ Finset.univ.filter fun S : Finset ι =>
      S.card = 9 ∧ 2 ≤ (badVerts i ∩ S).card := by
  obtain ⟨S, rfl⟩ := exists_inr_of_badTy_eq_true (Finset.mem_filter.mp hj).2
  exact (Finset.mem_filter_univ _).mpr
    ⟨S.2, two_le_card_inter_of_mem_nbr (Finset.mem_filter.mp hj).1⟩
end BSLambda.LLL
