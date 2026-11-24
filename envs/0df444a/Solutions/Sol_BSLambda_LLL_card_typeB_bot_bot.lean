-- Prove2me | solution 1 for BSLambda.LLL.card_typeB_bot_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:47.003231+00:00
-- url     : https://prove2.me/submissions/5b1bacaf-b1b6-47be-9f16-b22a6af75fd0

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
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_owner_bot
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_top_bot
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_top_owner
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_card_bot_of_top_eq_some
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_owner_ne_top
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_nonOwners
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_supp
public import Theorems.Thm_BSLambda_LLL_avoid_empty
public import Theorems.Thm_BSLambda_LLL_card_arcSet
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
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
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
theorem _root_.solution {d t : ℕ} (hT : IsDRTournamentWith Arc d t) {u v : ι} (huv : u ≠ v) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.bot ∧ v ∈ G.bot).card
      ≤ Nat.choose t 2 * (t - 2) := by
  have hinj : Function.Injective fun p : ι × ι ↦ (p.2, some p.1) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    exact Prod.ext h.2 h.1
  refine le_trans (card_flags_le_mul_choose (Arc := Arc)
      (H := (arcSet Arc (commonIn Arc u v)).image fun p ↦ (p.2, some p.1))
      (W := {u, v}) (c := 3) (N := t - 2) ?_ ?_ ?_ ?_ ?_) ?_
  · exact fun G hG ↦ hG.1
  · rintro G ⟨hAct, hane, hu, hv⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    refine Finset.mem_image.mpr ⟨(a, G.owner), mem_arcSet.2 ⟨⟨?_, ?_,
      (hAct.owner_ne_top ha).symm⟩, hAct.arc_top_owner ha⟩, by simp [ha]⟩
    · exact mem_commonIn.2 ⟨hAct.arc_top_bot ha hu, hAct.arc_top_bot ha hv⟩
    · exact mem_commonIn.2 ⟨hAct.arc_owner_bot hu, hAct.arc_owner_bot hv⟩
  · rintro G ⟨-, -, hu, hv⟩
    simp [Finset.insert_subset_iff, hu, hv]
  · rintro G ⟨hAct, hane, -, -⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    exact hAct.card_bot_of_top_eq_some ha
  · rintro G ⟨hAct, hane, hu, hv⟩
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    have hsub : ({u, v} : Finset ι) ⊆ headOut Arc (G.owner, G.top) :=
      Finset.insert_subset (hAct.bot_subset_headOut hu)
        (Finset.singleton_subset_iff.mpr (hAct.bot_subset_headOut hv))
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_pair huv, ha,
      headOut_some, hT.card_commonOut (hAct.owner_ne_top ha)]
  · simp only [Finset.card_image_of_injective _ hinj, card_arcSet hT.toIsTournament,
      hT.card_commonIn huv, Finset.card_pair huv, Nat.choose_one_right,
      Nat.reduceSub, le_refl]
end BSLambda.LLL
