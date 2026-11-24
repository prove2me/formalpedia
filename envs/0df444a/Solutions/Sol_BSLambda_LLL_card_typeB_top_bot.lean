-- Prove2me | solution 1 for BSLambda.LLL.card_typeB_top_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:20.925308+00:00
-- url     : https://prove2.me/submissions/cd78f5c6-738b-4617-a748-0794f55867c4

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_headOut_none
public import Theorems.Thm_BSLambda_LLL_headOut_some
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_bot_subset_headOut
public import Theorems.Thm_BSLambda_LLL_card_flags_le_mul_choose
public import Theorems.Thm_BSLambda_Construction_card_block
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst
public import Theorems.Thm_BSLambda_Construction_ind_eq_false_iff
public import Theorems.Thm_BSLambda_Construction_ind_eq_true_iff
public import Theorems.Thm_BSLambda_Construction_mem_block
public import Theorems.Thm_BSLambda_IsDRTournamentWith_card_middles
public import Theorems.Thm_BSLambda_IsTournament_ne_of_arc
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_owner_bot
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_top_owner
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_card_bot_of_top_eq_some
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_owner_ne_top
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_nonOwners
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_supp
public import Theorems.Thm_BSLambda_LLL_avoid_empty
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_mem_arcSet
public import Theorems.Thm_BSLambda_LLL_mem_avoid
public import Theorems.Thm_BSLambda_LLL_mem_discSet
public import Theorems.Thm_BSLambda_LLL_mem_fibre
public import Theorems.Thm_BSLambda_LLL_mem_missArcs
public import Theorems.Thm_BSLambda_LLL_mem_missSet
public import Theorems.Thm_BSLambda_LLL_mem_nbr
public import Theorems.Thm_BSLambda_LLL_mem_ownerGates
public import Theorems.Thm_BSLambda_LLL_mem_zeroSet
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_iff
public import Theorems.Thm_BSLambda_PartialAssign_mem_cube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_proj_apply
public import Theorems.Thm_BSLambda_PartialAssign_proj_sat
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_mem_commonIn
public import Theorems.Thm_BSLambda_mem_commonOut
public import Theorems.Thm_BSLambda_mem_inNbrs
public import Theorems.Thm_BSLambda_mem_middles
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.Construction.card_block
attribute [local simp] BSLambda.Construction.gateCoord_fst
attribute [local simp] BSLambda.Construction.ind_eq_false_iff
attribute [local simp] BSLambda.Construction.ind_eq_true_iff
attribute [local simp] BSLambda.Construction.mem_block
attribute [local simp] BSLambda.LLL.Flag1.mem_nonOwners
attribute [local simp] BSLambda.LLL.Flag1.mem_supp
attribute [local simp] BSLambda.LLL.avoid_empty
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.mem_arcSet
attribute [local simp] BSLambda.LLL.mem_avoid
attribute [local simp] BSLambda.LLL.mem_discSet
attribute [local simp] BSLambda.LLL.mem_fibre
attribute [local simp] BSLambda.LLL.mem_missArcs
attribute [local simp] BSLambda.LLL.mem_missSet
attribute [local simp] BSLambda.LLL.mem_nbr
attribute [local simp] BSLambda.LLL.mem_ownerGates
attribute [local simp] BSLambda.LLL.mem_zeroSet
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ
attribute [local simp] BSLambda.PartialAssign.dist_eq_zero_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_false_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_true_iff
attribute [local simp] BSLambda.PartialAssign.mem_cube
attribute [local simp] BSLambda.PartialAssign.mem_fixedSet
attribute [local simp] BSLambda.PartialAssign.mem_violSet
attribute [local simp] BSLambda.PartialAssign.proj_apply
attribute [local simp] BSLambda.PartialAssign.proj_sat
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.mem_commonIn
attribute [local simp] BSLambda.mem_commonOut
attribute [local simp] BSLambda.mem_inNbrs
attribute [local simp] BSLambda.mem_middles
attribute [local simp] BSLambda.mem_outNbrs
attribute [local simp] BSLambda.zeroInput_apply


attribute [local simp] BSLambda.LLL.headOut_none
attribute [local simp] BSLambda.LLL.headOut_some

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
open scoped Classical
namespace BSLambda.LLL
theorem _root_.solution {d t : ℕ} (hT : IsDRTournamentWith Arc d t)
    {u v : ι} (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top = some u ∧ v ∈ G.bot).card ≤ t * Nat.choose (t - 1) 2 := by
  refine le_trans (card_flags_le_mul_choose (Arc := Arc)
      (H := middles Arc u v ×ˢ {some u})
      (W := {v}) (c := 3) (N := t - 1) ?_ ?_ ?_ ?_ ?_) ?_
  · exact fun G hG ↦ hG.1
  · rintro G ⟨hAct, ha, hv⟩
    simp only [Finset.mem_product, mem_middles, Finset.mem_singleton, ha]
    exact ⟨⟨hAct.arc_top_owner ha, hAct.arc_owner_bot hv⟩, trivial⟩
  · exact fun G hG ↦ Finset.singleton_subset_iff.mpr hG.2.2
  · exact fun G hG ↦ hG.1.card_bot_of_top_eq_some hG.2.1
  · rintro G ⟨hAct, ha, hv⟩
    rw [← Finset.erase_eq, Finset.card_erase_of_mem (hAct.bot_subset_headOut hv), ha,
      headOut_some, hT.card_commonOut (hAct.owner_ne_top ha)]
  · have : Nontrivial ι := ⟨u, v, hT.ne_of_arc harc⟩
    have hmid : (middles Arc u v).card = t := hT.card_middles harc
    simp only [Finset.card_product, Finset.card_singleton, mul_one, hmid,
      Finset.card_singleton, Nat.reduceSub, le_refl]
end BSLambda.LLL
