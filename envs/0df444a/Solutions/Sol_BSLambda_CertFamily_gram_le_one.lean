-- Prove2me | solution 1 for BSLambda.CertFamily.gram_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:46.329841+00:00
-- url     : https://prove2.me/submissions/d637c2ed-dd76-40e3-990e-20a452f6da6c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_exists_pair_of_common_nbr
public import Theorems.Thm_BSLambda_eq_flipSet_singleton_of_common_nbr
public import Theorems.Thm_BSLambda_CertFamily_ind_flipSet_singleton_eq_true_or
public import Theorems.Thm_BSLambda_CertFamily_ind_eq_false_iff
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_ne
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
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
public import Theorems.Thm_BSLambda_gram_apply
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



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x y : Ones F.ind} (hxy : x ≠ y) : gram F.ind x y ≤ 1 := by
  rw [gram_apply, Nat.cast_le_one, Finset.card_le_one]
  intro z hz w hw
  rw [Finset.mem_filter_univ] at hz hw
  obtain ⟨p, q, hpq, hy⟩ := exists_pair_of_common_nbr (Subtype.coe_injective.ne hxy) hz.1 hz.2
  have hboth : ¬(F.ind (flipSet x.1 {p}) = false ∧ F.ind (flipSet x.1 {q}) = false) := by
    rcases F.ind_flipSet_singleton_eq_true_or hpq hy with h | h <;> simp [h]
  rcases eq_flipSet_singleton_of_common_nbr hpq hz.1 (hy ▸ hz.2) with hz1 | hz1 <;>
    rcases eq_flipSet_singleton_of_common_nbr hpq hw.1 (hy ▸ hw.2) with hw1 | hw1
  · exact Subtype.ext (hz1.trans hw1.symm)
  · exact absurd ⟨hz1 ▸ z.2, hw1 ▸ w.2⟩ hboth
  · exact absurd ⟨hw1 ▸ w.2, hz1 ▸ z.2⟩ hboth
  · exact Subtype.ext (hz1.trans hw1.symm)
end BSLambda.CertFamily
