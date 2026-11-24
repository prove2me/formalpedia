-- Prove2me | solution 1 for BSLambda.LLL.card_typeB_through_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:35.470266+00:00
-- url     : https://prove2.me/submissions/2d1d4171-862b-42a2-8c0b-41670dfa839a

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_headOut_none
public import Theorems.Thm_BSLambda_LLL_headOut_some
public import Theorems.Thm_BSLambda_LLL_card_typeB_top_owner
public import Theorems.Thm_BSLambda_LLL_card_typeB_top_bot
public import Theorems.Thm_BSLambda_LLL_card_typeB_owner_bot
public import Theorems.Thm_BSLambda_LLL_card_typeB_bot_bot
public import Theorems.Thm_BSLambda_Construction_card_block
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst
public import Theorems.Thm_BSLambda_Construction_ind_eq_false_iff
public import Theorems.Thm_BSLambda_Construction_ind_eq_true_iff
public import Theorems.Thm_BSLambda_Construction_mem_block
public import Theorems.Thm_BSLambda_IsTournament_arc_asymm
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_owner_bot
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_top_bot
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_arc_top_owner
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
theorem _root_.solution (hT : IsDRTournamentWith Arc 7005 3502)
    {u v : ι} (huv : u ≠ v) (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.supp ∧ v ∈ G.supp).card
      ≤ 71519595000 := by
  have hrev : Arc v u ≠ true := hT.arc_asymm harc
  have hsub : (Finset.univ.filter fun G : Flag1 ι ↦
        G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.supp ∧ v ∈ G.supp) ⊆
      ((Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ G.top = some u ∧ G.owner = v) ∪
        (Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ G.top = some u ∧ v ∈ G.bot)) ∪
      ((Finset.univ.filter fun G : Flag1 ι ↦
          G.Active Arc ∧ G.top ≠ none ∧ G.owner = u ∧ v ∈ G.bot) ∪
        (Finset.univ.filter fun G : Flag1 ι ↦
          G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.bot ∧ v ∈ G.bot)) := by
    intro G hG
    obtain ⟨hAct, hane, hu, hv⟩ := (Finset.mem_filter_univ _).mp hG
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hane
    simp only [Flag1.mem_supp, Flag1.mem_nonOwners, ha, Option.mem_some_iff] at hu hv
    simp only [Finset.mem_union, Finset.mem_filter_univ]
    rcases hu with rfl | rfl | hu
    · rcases hv with rfl | rfl | hv
      · exact absurd rfl huv
      · exact absurd (hAct.arc_top_owner ha) hrev
      · exact Or.inr (Or.inl ⟨hAct, hane, rfl, hv⟩)
    · rcases hv with rfl | rfl | hv
      · exact Or.inl (Or.inl ⟨hAct, ha, rfl⟩)
      · exact absurd rfl huv
      · exact Or.inl (Or.inr ⟨hAct, ha, hv⟩)
    · rcases hv with rfl | rfl | hv
      · exact absurd (hAct.arc_owner_bot hu) hrev
      · exact absurd (hAct.arc_top_bot ha hu) hrev
      · exact Or.inr (Or.inr ⟨hAct, hane, hu, hv⟩)
  have htop := card_typeB_top_owner hT huv
  have htopBottom := card_typeB_top_bot hT harc
  have hownerBottom := card_typeB_owner_bot hT huv
  have hbottom := card_typeB_bot_bot hT huv
  simp only [Nat.reduceSub] at htopBottom hownerBottom hbottom
  apply (Finset.card_le_card hsub).trans
  calc
    _ ≤ (Nat.choose 3502 3 + 3502 * Nat.choose 3501 2) +
        (3502 * Nat.choose 3501 2 + Nat.choose 3502 2 * 3500) := by
      apply (Finset.card_union_le _ _).trans
      apply add_le_add
      · apply (Finset.card_union_le _ _).trans
        exact add_le_add htop htopBottom
      · apply (Finset.card_union_le _ _).trans
        exact add_le_add hownerBottom hbottom
    _ ≤ 71519595000 := by
      norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
end BSLambda.LLL
