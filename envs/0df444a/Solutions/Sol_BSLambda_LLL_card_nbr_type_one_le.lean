-- Prove2me | solution 1 for BSLambda.LLL.card_nbr_type_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:17.323696+00:00
-- url     : https://prove2.me/submissions/0cd28eb7-187f-44c8-8085-3566a5581659

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_exists_inl_of_badTy_eq_false
public import Theorems.Thm_BSLambda_LLL_two_le_card_inter_of_mem_nbr
public import Theorems.Thm_BSLambda_LLL_exists_pair_subset_of_two_le_card_inter
public import Theorems.Thm_BSLambda_Construction_card_block
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst
public import Theorems.Thm_BSLambda_Construction_ind_eq_false_iff
public import Theorems.Thm_BSLambda_Construction_ind_eq_true_iff
public import Theorems.Thm_BSLambda_Construction_mem_block
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
theorem _root_.solution (i : BadIdx Arc) :
    ((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = false).card
      ≤ ∑ p ∈ (badVerts i).powersetCard 2,
          (Finset.univ.filter fun G : Flag1 ι => G.Active Arc ∧ p ⊆ G.supp).card := by
  classical
  set T := (nbr (badSupp (Arc := Arc)) i).filter (fun j ↦ badTy j = false)
  rcases Finset.eq_empty_or_nonempty T with hT | ⟨j0, hj0⟩
  · simp [hT]
  obtain ⟨F0, rfl⟩ := exists_inl_of_badTy_eq_false (Finset.mem_filter.mp hj0).2
  -- the flag `F0` is the fallback value that makes the map to flags total
  set f : BadIdx Arc → Flag1 ι := Sum.elim (fun F ↦ F.1) (fun _ ↦ F0.1)
  set B : Finset (Flag1 ι) :=
    ((badVerts i).powersetCard 2).biUnion
      (fun p ↦ Finset.univ.filter fun G : Flag1 ι ↦ G.Active Arc ∧ p ⊆ G.supp)
  have hmaps : ∀ j ∈ T, f j ∈ B := by
    intro j hj
    obtain ⟨p, hp, hpsub⟩ := exists_pair_subset_of_two_le_card_inter
      (two_le_card_inter_of_mem_nbr (Finset.mem_filter.mp hj).1)
    obtain ⟨F, rfl⟩ := exists_inl_of_badTy_eq_false (Finset.mem_filter.mp hj).2
    exact Finset.mem_biUnion.mpr ⟨p, hp, (Finset.mem_filter_univ _).mpr ⟨F.2, hpsub⟩⟩
  have hinj : Set.InjOn f (T : Set (BadIdx Arc)) := by
    intro j1 hj1 j2 hj2 hfe
    rw [Finset.mem_coe] at hj1 hj2
    obtain ⟨F1, rfl⟩ := exists_inl_of_badTy_eq_false (Finset.mem_filter.mp hj1).2
    obtain ⟨F2, rfl⟩ := exists_inl_of_badTy_eq_false (Finset.mem_filter.mp hj2).2
    exact congrArg Sum.inl (Subtype.ext hfe)
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans Finset.card_biUnion_le
end BSLambda.LLL
