-- Prove2me | solution 1 for BSLambda.LLL.card_nbr_two_two_le_D22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:33:21.649292+00:00
-- url     : https://prove2.me/submissions/ff407d17-16d4-45e1-9710-fdbc3164cd5c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_card_filter_two_le_card_inter_le
public import Theorems.Thm_BSLambda_LLL_card_nbr_type_two_two_le
public import Theorems.Thm_BSLambda_Numerics_D22_eq_sum
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
    (S : {S : Finset ι // S.card = 9}) :
    ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j => badTy j = true).card
      ≤ D22 := by
  classical
  have h1 : ((nbr (badSupp (Arc := Arc)) (Sum.inr S)).filter fun j ↦ badTy j = true).card
      ≤ (Finset.univ.filter fun T : Finset ι ↦
          T.card = 9 ∧ 2 ≤ (S.1 ∩ T).card).card - 1 := card_nbr_type_two_two_le S
  have h2 : (Finset.univ.filter fun T : Finset ι ↦ T.card = 9 ∧ 2 ≤ (S.1 ∩ T).card).card
      ≤ ∑ s ∈ Finset.Icc 2 S.1.card,
          S.1.card.choose s * (Fintype.card ι - S.1.card).choose (9 - s) :=
    card_filter_two_le_card_inter_le S.1 (le_of_eq S.2)
  have h3 : (∑ s ∈ Finset.Icc 2 S.1.card,
      S.1.card.choose s * (Fintype.card ι - S.1.card).choose (9 - s)) - 1 = D22 := by
    rw [S.2, hk]
    norm_num
    exact D22_eq_sum.symm
  omega
end BSLambda.LLL
