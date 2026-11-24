-- Prove2me | solution 1 for BSLambda.CertFamily.dist_eq_two_of_dist_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:04.393174+00:00
-- url     : https://prove2.me/submissions/333d7e35-ad82-45e2-be3b-7b678d2045f0

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_CertFamily_exists_flip_pair_of_dist_eq_one
public import Theorems.Thm_BSLambda_CertFamily_ind_eq_false_iff
public import Theorems.Thm_BSLambda_CertFamily_owner_sat
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_card_violSet
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_iff
public import Theorems.Thm_BSLambda_PartialAssign_mem_cube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet_iff_exists
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_proj_apply
public import Theorems.Thm_BSLambda_PartialAssign_proj_eq_of_sat_of_eq_off_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_proj_sat
public import Theorems.Thm_BSLambda_PartialAssign_violSet_eq_pair_of_conflict
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



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
open BSLambda.CertFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : CertFamily V ι)
namespace BSLambda.CertFamily
theorem _root_.solution {x y : Ones F.ind} (hne : gram F.ind x y ≠ 0)
    (hd : (F.P (F.owner y)).dist x.1 = 1) :
    (F.P (F.owner x)).dist y.1 = 2 ∧ x.1 = (F.P (F.owner x)).proj y.1 := by
  obtain ⟨p, q, hpq, hconf, hyf, hpi, -⟩ := F.exists_flip_pair_of_dist_eq_one hne hd
  have hxs := F.owner_sat x
  have hqi : q ∈ (F.P (F.owner x)).fixedSet :=
    PartialAssign.mem_fixedSet_iff_exists.2 (hconf.imp fun _ hb ↦ hb.1)
  have hviol : (F.P (F.owner x)).violSet y.1 = {p, q} := by
    rw [hyf]
    exact PartialAssign.violSet_eq_pair_of_conflict hxs (hyf ▸ F.owner_sat y) hconf hpi
  refine ⟨by rw [PartialAssign.dist_eq_card_violSet, hviol, Finset.card_pair hpq],
    (PartialAssign.proj_eq_of_sat_of_eq_off_fixedSet hxs fun v hv ↦ ?_).symm⟩
  have hvpq : v ∉ ({p, q} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    exacts [hv hpi, hv hqi]
  rw [hyf, flipSet_apply_of_notMem hvpq]
end BSLambda.CertFamily
