-- Prove2me | solution 1 for BSLambda.LLL.card_nbr_two_one_le_D21
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:54.252698+00:00
-- url     : https://prove2.me/submissions/c67fa892-9033-4d49-baaa-a71c5c0c5f5c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_card_nbr_type_one_le
public import Theorems.Thm_BSLambda_LLL_card_active_flag_through_pair
public import Theorems.Thm_BSLambda_Numerics_D21_eq_thirtysix_mul


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
    (S : {S : Finset ι // S.card = 9}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j => badTy j = false).card
      ≤ D21 := by
  classical
  have hle : ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j ↦ badTy j = false).card
      ≤ ∑ p ∈ (badVerts (Sum.inr S)).powersetCard 2,
          (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp).card :=
    card_nbr_type_one_le (i := Sum.inr S)
  have hcardS : (Finset.powersetCard 2 (S : Finset ι)).card = 36 := by
    rw [Finset.card_powersetCard, S.prop]
    decide
  have hsum : ∑ p ∈ (S : Finset ι).powersetCard 2,
      (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp).card
      ≤ (Finset.powersetCard 2 (S : Finset ι)).card * 214620087510 := by
    apply Finset.sum_le_card_nsmul
    intro p hp
    exact card_active_flag_through_pair hT (Finset.mem_powersetCard.mp hp).2
  rw [hcardS] at hsum
  rw [D21_eq_thirtysix_mul]
  exact hle.trans hsum
end BSLambda.LLL
