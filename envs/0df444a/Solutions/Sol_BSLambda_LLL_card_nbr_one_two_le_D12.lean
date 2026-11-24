-- Prove2me | solution 1 for BSLambda.LLL.card_nbr_one_two_le_D12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:33:13.823327+00:00
-- url     : https://prove2.me/submissions/2e1d4170-6249-47b7-96f4-50fae39b0253

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_card_filter_two_le_card_inter_le
public import Theorems.Thm_BSLambda_LLL_card_nbr_type_two_le
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_card_supp
public import Theorems.Thm_BSLambda_Numerics_D12_eq_sum
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (hk : Fintype.card ι = 14011)
    (F : {F : Flag1 ι // F.Active Arc}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j => badTy j = true).card
      ≤ D12 := by
  have h1 : (badVerts (Sum.inl F)).card = 5 := Flag1.Active.card_supp F.2
  calc ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j ↦ badTy j = true).card
      ≤ (Finset.univ.filter fun S : Finset ι ↦
          S.card = 9 ∧ 2 ≤ (badVerts (Sum.inl F) ∩ S).card).card :=
        card_nbr_type_two_le (Sum.inl F)
    _ ≤ ∑ s ∈ Finset.Icc 2 (badVerts (Sum.inl F)).card,
          (badVerts (Sum.inl F)).card.choose s *
            (Fintype.card ι - (badVerts (Sum.inl F)).card).choose (9 - s) :=
        card_filter_two_le_card_inter_le _ (by omega)
    _ = D12 := by
        rw [h1, hk]
        norm_num
        exact D12_eq_sum.symm
end BSLambda.LLL
