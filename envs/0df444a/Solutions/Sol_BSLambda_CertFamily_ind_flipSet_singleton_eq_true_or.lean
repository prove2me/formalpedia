-- Prove2me | solution 1 for BSLambda.CertFamily.ind_flipSet_singleton_eq_true_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:47.75381+00:00
-- url     : https://prove2.me/submissions/95337f7c-ccd1-4ebc-89cc-6c8fc8dba0d0

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_CertFamily_eq_conflictCoord
public import Theorems.Thm_BSLambda_CertFamily_ind_eq_false_iff
public import Theorems.Thm_BSLambda_CertFamily_ind_flipSet_singleton_eq_true
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_conflict_of_mem_fixedSet
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
public import Theorems.Thm_BSLambda_flipSet_pair_flipSet_singleton
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
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
theorem _root_.solution {x y : Ones F.ind} {p q : V} (hpq : p ≠ q)
    (hy : y.1 = flipSet x.1 {p, q}) :
    F.ind (flipSet x.1 {p}) = true ∨ F.ind (flipSet x.1 {q}) = true := by
  have hxs := F.owner_sat x
  have hys := F.owner_sat y
  have hne_p : x.1 p ≠ y.1 p := hy ▸ ne_flipSet_apply (Finset.mem_insert_self p {q})
  have hne_q : x.1 q ≠ y.1 q := hy ▸ ne_flipSet_apply (by simp)
  have hfree : p ∉ (F.P (F.owner x)).fixedSet ∨ q ∉ (F.P (F.owner x)).fixedSet ∨
      p ∉ (F.P (F.owner y)).fixedSet ∨ q ∉ (F.P (F.owner y)).fixedSet := by
    by_contra hc
    push Not at hc
    obtain ⟨hpi, hqi, hpj, hqj⟩ := hc
    by_cases hij : F.owner x = F.owner y
    · exact PartialAssign.notMem_fixedSet_of_apply_ne hxs (hij ▸ hys) hne_p hpi
    · exact hpq ((F.eq_conflictCoord hij
        (PartialAssign.conflict_of_mem_fixedSet hxs hys hpi hpj hne_p)).trans
        (F.eq_conflictCoord hij
          (PartialAssign.conflict_of_mem_fixedSet hxs hys hqi hqj hne_q)).symm)
  -- Flipping `y` at one of the two coordinates lands on the other midpoint of `x`.
  have hyq : flipSet y.1 {q} = flipSet x.1 {p} := by
    rw [hy, flipSet_pair_flipSet_singleton _ hpq]
  have hyp : flipSet y.1 {p} = flipSet x.1 {q} := by
    rw [hy, Finset.pair_comm, flipSet_pair_flipSet_singleton _ hpq.symm]
  rcases hfree with h | h | h | h
  · exact Or.inl (F.ind_flipSet_singleton_eq_true hxs h)
  · exact Or.inr (F.ind_flipSet_singleton_eq_true hxs h)
  · exact Or.inr (hyp ▸ F.ind_flipSet_singleton_eq_true hys h)
  · exact Or.inl (hyq ▸ F.ind_flipSet_singleton_eq_true hys h)
end BSLambda.CertFamily
