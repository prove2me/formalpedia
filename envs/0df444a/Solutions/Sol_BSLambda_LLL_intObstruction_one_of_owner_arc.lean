-- Prove2me | solution 1 for BSLambda.LLL.intObstruction_one_of_owner_arc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:06.924807+00:00
-- url     : https://prove2.me/submissions/b44ffa71-006d-46a1-afb9-b14cf3f428d5

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

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace BSLambda.LLL
theorem _root_.solution {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}
    {S : Finset ι} {h : ι} {Z : ι → Finset (Fin r)}
    (hgate : ∀ j ∈ S, Arc h j → γ h j ∈ Z j)
    (hbud : ∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ 1)
    {j : ι} (hj : j ∈ S) (hjh : j ≠ h) (harc : Arc h j = true) :
    Z j = {γ h j} ∧ ∀ k ∈ S, Arc j k = true → γ j k ∈ Z k := by
  have hmem : γ h j ∈ Z j := hgate j hj harc
  have hb := hbud j hj hjh
  have hsub : ({γ h j} : Finset (Fin r)) ⊆ Z j := Finset.singleton_subset_iff.mpr hmem
  have hpos : 1 ≤ (Z j).card := Finset.card_pos.mpr ⟨_, hmem⟩
  have hle : (Z j).card ≤ ({γ h j} : Finset (Fin r)).card := by
    simp only [Finset.card_singleton]
    omega
  refine ⟨(Finset.eq_of_subset_of_card_le hsub hle).symm, fun k hk hark ↦ ?_⟩
  have hf : missSet Arc γ Z S j = ∅ := Finset.card_eq_zero.1 (by omega)
  by_contra hcon
  exact absurd (hf ▸ mem_missSet.2 ⟨hk, hark, hcon⟩) (Finset.notMem_empty k)
end BSLambda.LLL
