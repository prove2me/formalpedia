-- Prove2me | solution 1 for BSLambda.LLL.intObstruction_two_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:00.818095+00:00
-- url     : https://prove2.me/submissions/1055fc58-e08c-4d1f-b617-81ab46a543e7

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_mem_ownerGates
public import Theorems.Thm_BSLambda_LLL_mem_arcSet
public import Theorems.Thm_BSLambda_LLL_mem_missSet
public import Theorems.Thm_BSLambda_LLL_missSet_subset_missSet
public import Theorems.Thm_BSLambda_LLL_mem_zeroSet
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_nonOwners
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_supp
public import Theorems.Thm_BSLambda_LLL_mem_missArcs
public import Theorems.Thm_BSLambda_LLL_mem_discSet
public import Theorems.Thm_BSLambda_LLL_missArcs_subset
public import Theorems.Thm_BSLambda_LLL_discSet_subset
public import Theorems.Thm_BSLambda_LLL_mem_branch2
public import Theorems.Thm_BSLambda_LLL_card_arcSet_erase
public import Theorems.Thm_BSLambda_LLL_intObstruction_two_nonowner
public import Theorems.Thm_BSLambda_LLL_card_miss_add_card_disc_le
public import Theorems.Thm_BSLambda_Construction_card_block
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst
public import Theorems.Thm_BSLambda_Construction_ind_eq_false_iff
public import Theorems.Thm_BSLambda_Construction_ind_eq_true_iff
public import Theorems.Thm_BSLambda_Construction_mem_block
public import Theorems.Thm_BSLambda_LLL_avoid_empty
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_mem_avoid
public import Theorems.Thm_BSLambda_LLL_mem_fibre
public import Theorems.Thm_BSLambda_LLL_mem_nbr
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
attribute [local simp] BSLambda.LLL.avoid_empty
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.mem_avoid
attribute [local simp] BSLambda.LLL.mem_fibre
attribute [local simp] BSLambda.LLL.mem_nbr
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


attribute [local simp] BSLambda.LLL.mem_ownerGates
attribute [local simp] BSLambda.LLL.mem_arcSet
attribute [local simp] BSLambda.LLL.mem_missSet
attribute [local gcongr] BSLambda.LLL.missSet_subset_missSet
attribute [local simp] BSLambda.LLL.mem_zeroSet
attribute [local simp] BSLambda.LLL.Flag1.mem_nonOwners
attribute [local simp] BSLambda.LLL.Flag1.mem_supp
attribute [local simp] BSLambda.LLL.mem_missArcs
attribute [local simp] BSLambda.LLL.mem_discSet

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
namespace BSLambda.LLL
theorem _root_.solution [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι} (hh : h ∈ S) {ω : GateCfg ι r}
    (hobs : IntObstruction Arc 2 S h (toGamma ω)) :
    ∃ (L : Finset ι) (w : (j : ι) → j ∈ L → Fin r) (X : Finset (ι × ι)),
      L ⊆ S.erase h ∧ X ⊆ arcSet Arc (S.erase h) ∧ X.card + L.card = 8 ∧
        ω ∈ branch2 Arc S h L w X := by
  classical
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  have hnono : ∀ j ∈ S.erase h, ∃ z : Fin r, Z j ⊆ {toGamma ω h j, z} := fun j hj ↦
    (intObstruction_two_nonowner hT hh hZh hgate hj
      (hbud j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj))).1
  refine ⟨discSet (toGamma ω) Z (S.erase h) h,
    fun j hj ↦ (hnono j (discSet_subset hj)).choose, ?_⟩
  have hle := card_miss_add_card_disc_le hT hS hh hZh hgate hbud
  have hcard8 : (S.erase h).card = 8 := by rw [Finset.card_erase_of_mem hh, hS]
  have hAA : (arcSet Arc (S.erase h)).card = 28 := card_arcSet_erase hT hS hh
  obtain ⟨X, hX₀X, hXsub, hXcard⟩ := Finset.exists_subsuperset_card_eq
    (missArcs_subset (Arc := Arc) (γ := toGamma ω) (Z := Z) (T := S.erase h))
    (n := 8 - (discSet (toGamma ω) Z (S.erase h) h).card) (by omega) (by omega)
  refine ⟨X, discSet_subset, hXsub, by omega, mem_branch2.2 fun p hp hpX ↦ ?_⟩
  have hmem : toGamma ω p.1 p.2 ∈ Z p.2 := by
    by_contra hc
    exact hpX (hX₀X (mem_missArcs.2 ⟨hp, hc⟩))
  by_cases hpL : p.2 ∈ discSet (toGamma ω) Z (S.erase h) h
  · rw [dif_pos hpL]
    have hspec := (hnono p.2 (discSet_subset hpL)).choose_spec hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hspec
    simpa [toGamma] using hspec
  · left
    have hsub : Z p.2 ⊆ {toGamma ω h p.2} :=
      not_not.1 fun hc ↦ hpL (mem_discSet.2 ⟨(mem_arcSet.1 hp).1.2.1, hc⟩)
    simpa [toGamma] using Finset.mem_singleton.mp (hsub hmem)
end BSLambda.LLL
