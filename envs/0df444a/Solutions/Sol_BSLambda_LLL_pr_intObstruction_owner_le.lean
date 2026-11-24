-- Prove2me | solution 1 for BSLambda.LLL.pr_intObstruction_owner_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:04.970803+00:00
-- url     : https://prove2.me/submissions/99ad86a0-9664-4d76-81f7-4f52346f4fa2

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_card_arcSet_erase
public import Theorems.Thm_BSLambda_LLL_obs2_subset_branches
public import Theorems.Thm_BSLambda_LLL_pr_branch2_le
public import Theorems.Thm_BSLambda_LLL_sum_branch_pow_eq
public import Theorems.Thm_BSLambda_LLL_pr_biUnion_le
public import Theorems.Thm_BSLambda_LLL_pr_le_of_subset_biUnion


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
open scoped Classical
namespace BSLambda.LLL
theorem _root_.solution [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι} (hh : h ∈ S) :
    pr (β := fun _ : ι × ι => Fin r)
        (Finset.univ.filter fun ω : GateCfg ι r => IntObstruction Arc 2 S h (toGamma ω))
      ≤ (radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20 := by
  have hAA : (arcSet Arc (S.erase h)).card = 28 := card_arcSet_erase hT hS hh
  have h1 := pr_le_of_subset_biUnion (β := fun _ : ι × ι ↦ Fin r) _ _
      (obs2_subset_branches hT hS hh)
  apply h1.trans
  rw [← sum_branch_pow_eq (r := r) hh hS hAA]
  refine Finset.sum_le_sum fun L _ ↦ ?_
  apply (pr_biUnion_le _ _).trans
  refine Finset.sum_le_sum fun w _ ↦ ?_
  apply (pr_biUnion_le _ _).trans
  refine Finset.sum_le_sum fun X hX ↦ ?_
  have hXmem := Finset.mem_powersetCard.mp hX
  have hbr := pr_branch2_le (r := r) w hXmem.1
  rwa [hXmem.2] at hbr
end BSLambda.LLL
