-- Prove2me | solution 1 for BSLambda.LLL.card_nbr_one_one_le_D11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:53.808712+00:00
-- url     : https://prove2.me/submissions/9879de32-c796-4c92-b294-a9dc8a19f212

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_card_nbr_type_one_le
public import Theorems.Thm_BSLambda_LLL_card_active_flag_through_pair
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_card_supp


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (hT : IsDRTournamentWith Arc 7005 3502)
    (F : {F : Flag1 ι // F.Active Arc}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j => badTy j = false).card
      ≤ D11 := by
  classical
  have h1 : ((nbr (badSupp (Arc := Arc)) (Sum.inl F)).filter fun j ↦ badTy j = false).card
      ≤ ∑ p ∈ (badVerts (Sum.inl F)).powersetCard 2,
          (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp).card :=
    card_nbr_type_one_le _
  have hverts : badVerts (Sum.inl F) = F.1.supp := rfl
  rw [hverts] at h1
  have hle : (∑ p ∈ F.1.supp.powersetCard 2,
          (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp).card)
      ≤ Finset.card (F.1.supp.powersetCard 2) * 214620087510 := by
    apply Finset.sum_le_card_nsmul
    intro p hp
    exact card_active_flag_through_pair hT (Finset.mem_powersetCard.mp hp).2
  refine (h1.trans hle).trans ?_
  rw [Finset.card_powersetCard, (Flag1.Active.card_supp F.2 : F.1.supp.card = 5), D11]
  decide
end BSLambda.LLL
