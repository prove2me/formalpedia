-- Prove2me | solution 1 for BSLambda.CertFamily.gram_eq_zero_of_owner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:32.289191+00:00
-- url     : https://prove2.me/submissions/56b1a182-5465-4a41-b9ba-ce1d74166536

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_exists_pair_of_common_nbr
public import Theorems.Thm_BSLambda_eq_flipSet_singleton_of_common_nbr
public import Theorems.Thm_BSLambda_CertFamily_ind_eq_false_iff
public import Theorems.Thm_BSLambda_CertFamily_mem_fixedSet_of_ind_flipSet_singleton_eq_false
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_ne
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_iff
public import Theorems.Thm_BSLambda_PartialAssign_mem_cube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_notMem_fixedSet_of_apply_ne
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
public import Theorems.Thm_BSLambda_gram_ne_zero_iff
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_ne_flipSet_apply
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
theorem _root_.solution {x y : Ones F.ind} (hxy : x ≠ y)
    (h : F.owner x = F.owner y) : gram F.ind x y = 0 := by
  by_contra hne
  obtain ⟨z, hxz, hyz⟩ := gram_ne_zero_iff.1 hne
  obtain ⟨p, q, hpq, hy⟩ := exists_pair_of_common_nbr (Subtype.coe_injective.ne hxy) hxz hyz
  have hxs := F.owner_sat x
  have hys : (F.P (F.owner x)).Sat y.1 := h ▸ F.owner_sat y
  -- Either midpoint is a free flip of `x`, hence positive, contradicting `z.2`.
  have key {r : V} (hr : r ∈ ({p, q} : Finset V)) (hz : z.1 = flipSet x.1 {r}) : False :=
    PartialAssign.notMem_fixedSet_of_apply_ne hxs hys (hy ▸ ne_flipSet_apply hr)
      (F.mem_fixedSet_of_ind_flipSet_singleton_eq_false hxs (hz ▸ z.2))
  rcases eq_flipSet_singleton_of_common_nbr hpq hxz (hy ▸ hyz) with h1 | h1
  · exact key (Finset.mem_insert_self p {q}) h1
  · exact key (by simp) h1
end BSLambda.CertFamily
