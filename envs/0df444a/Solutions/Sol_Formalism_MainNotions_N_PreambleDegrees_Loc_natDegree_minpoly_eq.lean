-- Prove2me | solution 1 for Formalism.MainNotions.N.PreambleDegrees.Loc.natDegree_minpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:52.157109+00:00
-- url     : https://prove2.me/submissions/08a2e43d-3765-434d-a6b8-85a9868d52e5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_one_lt_l
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_Kur_zpow
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_one_sub_eq
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_one_sub_pow
import Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_minpoly_dvd_cyclotomic
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.Tmap_mk
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.PreambleDegrees Formalism.MainNotions.N.PreambleDegrees.Loc
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups Polynomial
variable {l : ℕ} [Fact l.Prime]
variable (l)
variable {l}
variable {F : IntermediateField ℚ_[l] (Om l)}
namespace Formalism.MainNotions.N.PreambleDegrees.Loc
theorem _root_.solution (hF : F ≤ MaximalUnramifiedExtension l) {k : ℕ} (hk : 0 < k) {z : Om l}
    (hz : IsPrimitiveRoot z (l ^ k)) : (minpoly F z).natDegree = (l ^ k).totient := by
  have hl := (Fact.out : l.Prime)
  have hpos : 0 < l ^ k := pow_pos hl.pos k
  have hint : IsIntegral F z := ⟨_, cyclotomic.monic _ _, by
    rw [eval₂_eq_eval_map, map_cyclotomic]
    exact (hz.isRoot_cyclotomic hpos).eq_zero⟩
  have hle : (minpoly F z).natDegree ≤ (l ^ k).totient := by
    have h := natDegree_le_of_dvd (minpoly_dvd_cyclotomic (F := F) hz) (cyclotomic_ne_zero (l ^ k) F)
    rwa [natDegree_cyclotomic] at h
  set m := minpoly F z with hm
  set P := m.map (algebraMap F (Om l)) with hP
  have hd : 0 < m.natDegree := minpoly.natDegree_pos hint
  have hmon : P.Monic := (minpoly.monic hint).map _
  have hsplit := IsAlgClosed.splits P
  haveI : NeZero ((l ^ k : ℕ) : Om l) := ⟨by exact_mod_cast hpos.ne'⟩
  have hroots : ∀ a ∈ P.roots, IsPrimitiveRoot a (l ^ k) := by
    intro a ha
    rw [mem_roots hmon.ne_zero] at ha
    have hdvd : P ∣ cyclotomic (l ^ k) (Om l) := by
      rw [← map_cyclotomic (l ^ k) (algebraMap F (Om l))]
      exact Polynomial.map_dvd _ (minpoly_dvd_cyclotomic hz)
    have hr : IsRoot (cyclotomic (l ^ k) (Om l)) a := by
      obtain ⟨q, hq⟩ := hdvd
      rw [IsRoot, hq, eval_mul, ha.eq_zero, zero_mul]
    exact isRoot_cyclotomic_iff.mp hr
  have hcard : Multiset.card P.roots = m.natDegree := by
    first
    | exact (splits_iff_card_roots.mp hsplit).trans (natDegree_map _)
    | exact (natDegree_eq_card_roots' hsplit).symm.trans (natDegree_map _)
    | (rw [hP, natDegree_map]; exact (IsAlgClosed.card_roots_eq_natDegree).trans (natDegree_map _))
  have heval : P.eval 1 = (P.roots.map fun a => 1 - a).prod := by
    have hPdeg : P.natDegree = m.natDegree := natDegree_map _
    conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (hcard.trans hPdeg.symm)]
    rw [eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hnorm : ‖(P.roots.map fun a => 1 - a).prod‖ = ‖1 - z‖ ^ m.natDegree := by
    rw [← hcard]
    have hr : ∀ a ∈ P.roots, ‖1 - a‖ = ‖1 - z‖ := fun a ha => norm_one_sub_eq (hroots a ha) hz
    generalize P.roots = s at hr ⊢
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ,
        ih (fun b hb => hr b (Multiset.mem_cons_of_mem hb)), hr a (Multiset.mem_cons_self a s)]
      ring
  have hmem : P.eval 1 ∈ MaximalUnramifiedExtension l := by
    rw [hP, eval_one_map]
    exact hF (m.eval 1).2
  have hz1 : z ≠ 1 := hz.ne_one (Nat.one_lt_pow hk.ne' hl.one_lt)
  have hrpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hval : ‖P.eval 1‖ = ‖1 - z‖ ^ m.natDegree := by rw [heval, hnorm]
  have hne : P.eval 1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hval
    exact (pow_pos hrpos _).ne' hval.symm
  obtain ⟨j, hj⟩ := norm_Kur_zpow hmem hne
  have hφ := norm_one_sub_pow hk hz
  have e1 : ‖1 - z‖ ^ (m.natDegree * (l ^ k).totient) = (l : ℝ) ^ (-(m.natDegree : ℤ)) := by
    rw [mul_comm, pow_mul, hφ, inv_pow, zpow_neg, zpow_natCast]
  have e2 : ‖1 - z‖ ^ (m.natDegree * (l ^ k).totient) = (l : ℝ) ^ (j * (l ^ k).totient : ℤ) := by
    rw [pow_mul, ← hval, hj, zpow_mul, zpow_natCast]
  have hinj : -(m.natDegree : ℤ) = j * (l ^ k).totient :=
    zpow_right_injective₀ (zero_lt_one.trans one_lt_l) one_lt_l.ne' (e1.symm.trans e2)
  have hφpos : 0 < (l ^ k).totient := by
    first
    | exact Nat.totient_pos.mpr hpos
    | exact Nat.totient_pos hpos
  have hj' : j ≤ -1 := by
    by_contra hc
    push_neg at hc
    have : (0 : ℤ) ≤ j * (l ^ k).totient := mul_nonneg (by omega) (by positivity)
    omega
  have hge : ((l ^ k).totient : ℤ) ≤ m.natDegree := by nlinarith
  have : (l ^ k).totient ≤ m.natDegree := by exact_mod_cast hge
  omega
end Formalism.MainNotions.N.PreambleDegrees.Loc
