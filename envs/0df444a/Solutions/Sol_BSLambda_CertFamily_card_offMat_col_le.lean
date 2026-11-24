-- Prove2me | solution 1 for BSLambda.CertFamily.card_offMat_col_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:05.940587+00:00
-- url     : https://prove2.me/submissions/cfee8e65-3632-4ae2-a64f-d608075b95e2

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Theorems.Thm_BSLambda_CertFamily_offMat_ne_zero_iff
public import Theorems.Thm_BSLambda_CertFamily_dist_eq_two_of_dist_eq_one
public import Theorems.Thm_BSLambda_CertFamily_ind_eq_false_iff
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_iff
public import Theorems.Thm_BSLambda_PartialAssign_mem_cube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_proj_apply
public import Theorems.Thm_BSLambda_PartialAssign_proj_sat
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.CertFamily.ind_eq_false_iff
attribute [local simp] BSLambda.PartialAssign.dist_eq_zero_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_false_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_true_iff
attribute [local simp] BSLambda.PartialAssign.mem_cube
attribute [local simp] BSLambda.PartialAssign.mem_fixedSet
attribute [local simp] BSLambda.PartialAssign.mem_violSet
attribute [local simp] BSLambda.PartialAssign.proj_apply
attribute [local simp] BSLambda.PartialAssign.proj_sat
attribute [local simp] BSLambda.card_nbrs
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.sum_adj_row
attribute [local simp] BSLambda.zeroInput_apply


section
@[expose] public section
namespace BSLambda
namespace CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
private theorem eq_proj_of_offMat_ne_zero {x y : Ones F.ind} (h : F.offMat x y ≠ 0) :
    x.1 = (F.P (F.owner x)).proj y.1 := by
  obtain ⟨-, hdist, hgram⟩ := F.offMat_ne_zero_iff.1 h
  exact (F.dist_eq_two_of_dist_eq_one hgram hdist).2
end CertFamily
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.CertFamily
open scoped Matrix Matrix.Norms.L2Operator
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution (y : Ones F.ind) :
    (Finset.univ.filter fun x : Ones F.ind => F.offMat x y ≠ 0).card ≤ F.B := by
  refine (Finset.card_le_card_of_injOn F.owner ?_ ?_).trans
    (F.listTwo (F.owner y) y.1 (F.owner_sat y))
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter_univ] at hx ⊢
    obtain ⟨hown, hdist, hgram⟩ := F.offMat_ne_zero_iff.1 hx
    exact ⟨hown, (F.dist_eq_two_of_dist_eq_one hgram hdist).1.le⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter_univ] at hx₁ hx₂
    refine Subtype.ext ?_
    rw [F.eq_proj_of_offMat_ne_zero hx₁, heq, ← F.eq_proj_of_offMat_ne_zero hx₂]
end BSLambda.CertFamily
