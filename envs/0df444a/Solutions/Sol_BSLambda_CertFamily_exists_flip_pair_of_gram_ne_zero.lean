-- Prove2me | solution 1 for BSLambda.CertFamily.exists_flip_pair_of_gram_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:06.030572+00:00
-- url     : https://prove2.me/submissions/14518447-3a61-4a31-ba00-43d7f0a30779

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_exists_pair_of_common_nbr
public import Theorems.Thm_BSLambda_eq_flipSet_singleton_of_common_nbr
public import Theorems.Thm_BSLambda_CertFamily_owner_ne_of_gram_ne_zero
public import Theorems.Thm_BSLambda_CertFamily_conflict_conflictCoord
public import Theorems.Thm_BSLambda_CertFamily_eq_conflictCoord
public import Theorems.Thm_BSLambda_CertFamily_ind_eq_false_iff
public import Theorems.Thm_BSLambda_CertFamily_mem_fixedSet_of_ind_flipSet_singleton_eq_false
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_ne
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_conflict_of_mem_fixedSet
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
public import Theorems.Thm_BSLambda_flipSet_pair_flipSet_singleton
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


section
@[expose] public section
namespace BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
private theorem exists_flip_pair_of_ind_flipSet_singleton_eq_false {x y : Ones F.ind}
    (hij : F.owner x ≠ F.owner y) {a b : V} (hab : a ≠ b) (hyf : y.1 = flipSet x.1 {a, b})
    (hfalse : F.ind (flipSet x.1 {a}) = false) :
    ∃ p q : V, p ≠ q ∧ (F.P (F.owner x)).Conflict (F.P (F.owner y)) q ∧
      y.1 = flipSet x.1 {p, q} ∧
      ((p ∈ (F.P (F.owner x)).fixedSet ∧ p ∉ (F.P (F.owner y)).fixedSet) ∨
        (p ∈ (F.P (F.owner y)).fixedSet ∧ p ∉ (F.P (F.owner x)).fixedSet)) := by
  have hxs := F.owner_sat x
  have hys := F.owner_sat y
  -- Undoing the `b`-half of the pair flip turns `y` into the same negative midpoint.
  have hswap : flipSet y.1 {b} = flipSet x.1 {a} := by
    rw [hyf, flipSet_pair_flipSet_singleton _ hab]
  have hai := F.mem_fixedSet_of_ind_flipSet_singleton_eq_false hxs hfalse
  have hbj := F.mem_fixedSet_of_ind_flipSet_singleton_eq_false hys (hswap ▸ hfalse)
  have hne_a : x.1 a ≠ y.1 a := hyf ▸ ne_flipSet_apply (Finset.mem_insert_self a {b})
  have hne_b : x.1 b ≠ y.1 b := hyf ▸ ne_flipSet_apply (by simp)
  have hr := F.conflict_conflictCoord hij
  -- Outside `{a, b}` the two points agree, so the conflict coordinate lies inside it.
  have hrmem : F.conflictCoord hij = a ∨ F.conflictCoord hij = b := by
    by_contra hc
    push Not at hc
    refine hr.ne hxs hys ?_
    rw [hyf, flipSet_apply_of_notMem (by simp [hc.1, hc.2])]
  rcases hrmem with hra | hrb
  · refine ⟨b, a, hab.symm, hra ▸ hr, ?_, Or.inr ⟨hbj, fun hbi ↦ hab.symm ?_⟩⟩
    · rw [hyf, Finset.pair_comm]
    · exact (F.eq_conflictCoord hij
        (PartialAssign.conflict_of_mem_fixedSet hxs hys hbi hbj hne_b)).trans hra
  · refine ⟨a, b, hab, hrb ▸ hr, hyf, Or.inl ⟨hai, fun haj ↦ hab ?_⟩⟩
    exact (F.eq_conflictCoord hij
      (PartialAssign.conflict_of_mem_fixedSet hxs hys hai haj hne_a)).trans hrb
end CertFamily
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x y : Ones F.ind} (hxy : x ≠ y)
    (hne : gram F.ind x y ≠ 0) :
    ∃ p q : V, p ≠ q ∧ (F.P (F.owner x)).Conflict (F.P (F.owner y)) q ∧
      y.1 = flipSet x.1 {p, q} ∧
      ((p ∈ (F.P (F.owner x)).fixedSet ∧ p ∉ (F.P (F.owner y)).fixedSet) ∨
        (p ∈ (F.P (F.owner y)).fixedSet ∧ p ∉ (F.P (F.owner x)).fixedSet)) := by
  obtain ⟨z, hxz, hyz⟩ := gram_ne_zero_iff.1 hne
  obtain ⟨p, q, hpq, hyf⟩ := exists_pair_of_common_nbr (Subtype.coe_injective.ne hxy) hxz hyz
  have hij := F.owner_ne_of_gram_ne_zero hxy hne
  -- Whichever of the two midpoints `z` is, it is negative.
  rcases eq_flipSet_singleton_of_common_nbr hpq hxz (hyf ▸ hyz) with h1 | h1
  · exact F.exists_flip_pair_of_ind_flipSet_singleton_eq_false hij hpq hyf (h1 ▸ z.2)
  · refine F.exists_flip_pair_of_ind_flipSet_singleton_eq_false hij hpq.symm ?_ (h1 ▸ z.2)
    rw [hyf, Finset.pair_comm]
end BSLambda.CertFamily
