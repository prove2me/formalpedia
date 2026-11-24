-- Prove2me | solution 1 for BSLambda.LLL.card_arcSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:07.694793+00:00
-- url     : https://prove2.me/submissions/f3179b3b-e6ea-496b-ab4c-9bc70db423db

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_card_arcSet_swap
public import Theorems.Thm_BSLambda_LLL_arcSet_union_arcSet_swap
public import Theorems.Thm_BSLambda_LLL_disjoint_arcSet_arcSet_swap

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {T : Finset ι} {p : ι × ι}
variable (hT : IsTournament Arc)
include hT
omit [DecidableEq ι]
namespace BSLambda.LLL
theorem _root_.solution (T : Finset ι) : (arcSet Arc T).card = Nat.choose T.card 2 := by
  classical
  have hcard := congrArg Finset.card (arcSet_union_arcSet_swap hT T)
  rw [Finset.card_union_of_disjoint (disjoint_arcSet_arcSet_swap hT T),
    card_arcSet_swap Arc T, Finset.offDiag_card] at hcard
  have hmul : T.card * (T.card - 1) = T.card * T.card - T.card := by
    rw [Nat.mul_sub, Nat.mul_one]
  rw [Nat.choose_two_right, hmul]
  generalize T.card * T.card - T.card = N at hcard ⊢
  omega
end BSLambda.LLL
