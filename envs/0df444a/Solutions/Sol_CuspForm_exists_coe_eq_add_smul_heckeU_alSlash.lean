-- Prove2me | solution 1 for CuspForm.exists_coe_eq_add_smul_heckeU_alSlash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3678fe28-4677-5ab3-94b9-4fb506a16179

import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash

set_option autoImplicit false

open CuspForm ModularFormClass
open scoped MatrixGroups ModularForm

namespace RC1

namespace TRWAux

variable {M q : ℕ} (A : ModularForm.AtkinLehnerDatum M q)

private def gamMat (j : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![A.a, A.a * j + A.b; (A.R : ℤ), (A.R : ℤ) * j + q]

private lemma det_gamMat (j : ℤ) : (gamMat A j).det = 1 := by
  rw [gamMat, Matrix.det_fin_two_of]; linear_combination A.bezout

private def gam (j : ℤ) : SL(2, ℤ) := ⟨gamMat A j, det_gamMat A j⟩

@[scoped simp] private lemma gam_apply (j : ℤ) (i i' : Fin 2) : (gam A j) i i' = gamMat A j i i' := rfl

private lemma gam_mem (j : ℤ) : gam A j ∈ CongruenceSubgroup.Gamma0 A.R := by
  rw [CongruenceSubgroup.Gamma0_mem, gam_apply]
  simp [gamMat]

@[scoped simp] private lemma gam_coe (j : ℤ) : ((gam A j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = gamMat A j := rfl

private lemma slash_alGL_heckeMatrix_apply [NeZero M] (k : ℤ) (j : ℕ) (F : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    ((F ∣[k] A.alGL) ∣[k] ModularForm.heckeMatrix q j) τ =
      (q : ℂ) ^ (k - 2) * (F ∣[k] (gam A j : GL (Fin 2) ℝ)) τ := by
  have hq0 : q ≠ 0 := A.q_pos.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hz' : ((ModularForm.heckeMatrix q j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / q :=
    ModularForm.coe_heckeMatrix_smul hq0 j τ
  have hnum : (q : ℂ) * (A.a : ℂ) * (((τ : ℂ) + j) / q) + (A.b : ℂ) =
      (A.a : ℂ) * (τ : ℂ) + ((A.a : ℂ) * j + (A.b : ℂ)) := by
    field_simp; ring
  have hdenv : (q : ℂ) * (A.R : ℂ) * (((τ : ℂ) + j) / q) + (q : ℂ) =
      (A.R : ℂ) * (τ : ℂ) + ((A.R : ℂ) * j + (q : ℂ)) := by
    field_simp; ring
  have hpt : A.alGL • (ModularForm.heckeMatrix q j • τ) = gam A j • τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos A.det_alGL_pos, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hz', gam_apply, gamMat,
      ModularForm.AtkinLehnerDatum.alGL_coe, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', eq_intCast, Int.cast_mul, Int.cast_natCast,
      Int.cast_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_intCast,
      Complex.ofReal_add, algebraMap_int_eq]
    rw [hnum, hdenv]
  have hden_eq : UpperHalfPlane.denom A.alGL ((ModularForm.heckeMatrix q j • τ : UpperHalfPlane) : ℂ) =
      UpperHalfPlane.denom (gam A j : GL (Fin 2) ℝ) (τ : ℂ) := by
    simp only [UpperHalfPlane.denom, hz', gam_coe, gamMat, ModularForm.AtkinLehnerDatum.alGL_coe,
      Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
      eq_intCast, Int.cast_mul, Int.cast_natCast, Int.cast_add, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_add, algebraMap_int_eq,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
    rw [hdenv]
  rw [ModularForm.slash_heckeMatrix_apply k hq0, ModularForm.slash_apply,
    ModularForm.AtkinLehnerDatum.σ_alGL_apply, ModularForm.AtkinLehnerDatum.val_det_alGL, hpt, hden_eq,
    ← ModularForm.SL_slash, ModularForm.SL_slash_apply]
  simp only [Nat.abs_cast, Complex.ofReal_natCast]
  have hz : (q : ℂ) ^ (k - 1) = (q : ℂ) ^ (k - 2) * q := by
    rw [show k - 1 = (k - 2) + 1 by ring, zpow_add_one₀ hqC]
  rw [hz]
  field_simp

private lemma smul_heckeU_alSlash [NeZero M] (k : ℤ) (F : UpperHalfPlane → ℂ) :
    (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k F) =
      ∑ j ∈ Finset.range q, F ∣[k] (gam A (j : ℕ) : GL (Fin 2) ℝ) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast A.q_pos.ne'
  ext τ
  simp only [Pi.smul_apply, ModularForm.heckeU, ModularForm.alSlash_def, Finset.sum_apply, smul_eq_mul,
    Finset.mul_sum, slash_alGL_heckeMatrix_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← zpow_add₀ hqC, show 2 - k + (k - 2) = 0 by ring, zpow_zero, one_mul]

private lemma Gamma0_le_of_dvd {R' M' : ℕ} (h : R' ∣ M') :
    CongruenceSubgroup.Gamma0 M' ≤ CongruenceSubgroup.Gamma0 R' := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact (Int.natCast_dvd_natCast.mpr h).trans hγ

private lemma gam_mul_gam_inv_apply_10 (i j : ℤ) :
    ((gam A i * (gam A j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (A.R : ℤ) ^ 2 * (j - i) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, gam_coe, gamMat,
    Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  ring

private lemma gam_mul_apply_10 (j : ℤ) (γ : SL(2, ℤ)) :
    ((gam A j * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      (A.R : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + ((A.R : ℤ) * j + q) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, gam_coe, gamMat, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val']

private lemma isCoprime_q_R : IsCoprime (q : ℤ) (A.R : ℤ) :=
  ⟨A.a, -A.b, by linear_combination A.bezout⟩

private lemma mem_Gamma0_iff (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma0 N ↔ (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

private lemma not_gam_mem [NeZero M] (hq : q.Prime) (j : ℤ) : gam A j ∉ CongruenceSubgroup.Gamma0 M := by
  rw [mem_Gamma0_iff, gam_coe]
  simp only [gamMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Int.natCast_dvd_natCast]
  intro h
  have hR := A.R_pos
  have hle : M ≤ A.R := Nat.le_of_dvd hR h
  have h2 : 2 * A.R ≤ M :=
    calc 2 * A.R ≤ q * A.R := Nat.mul_le_mul_right _ hq.two_le
      _ = M := A.hM.symm
  omega

private lemma gam_mul_gam_inv_mem_iff [NeZero M] (i j : ℤ) :
    gam A i * (gam A j)⁻¹ ∈ CongruenceSubgroup.Gamma0 M ↔ (q : ℤ) ∣ j - i := by
  have hMz : (M : ℤ) = (q : ℤ) * (A.R : ℤ) := by exact_mod_cast A.hM
  rw [mem_Gamma0_iff, gam_mul_gam_inv_apply_10, hMz, pow_two, mul_assoc]
  have hR0 : (A.R : ℤ) ≠ 0 := by exact_mod_cast A.R_pos.ne'
  rw [mul_comm (q : ℤ) (A.R : ℤ), mul_dvd_mul_iff_left hR0]
  constructor
  · intro h
    exact (isCoprime_q_R A).dvd_of_dvd_mul_left h
  · intro h
    exact Dvd.dvd.mul_left h _

private lemma exists_gam_mul_mem [NeZero M] (hq : q.Prime) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 A.R) (hγM : γ ∉ CongruenceSubgroup.Gamma0 M) :
    ∃ j : ℕ, j < q ∧ gam A j * γ ∈ CongruenceSubgroup.Gamma0 M := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hMz : (M : ℤ) = (q : ℤ) * (A.R : ℤ) := by exact_mod_cast A.hM
  rw [mem_Gamma0_iff] at hγ hγM
  obtain ⟨w, hw⟩ := hγ
  rw [hMz, hw] at hγM
  have hqw : ¬ (q : ℤ) ∣ w := fun h => hγM (by rw [mul_comm (q : ℤ)]; exact mul_dvd_mul_left _ h)
  have hRw : ((A.R : ZMod q) * (w : ZMod q)) ≠ 0 := by
    intro h0
    have h1 : ((((A.R : ℤ) * w : ℤ)) : ZMod q) = 0 := by push_cast; exact_mod_cast h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    exact hqw ((isCoprime_q_R A).dvd_of_dvd_mul_left h1)
  set x : ZMod q := -(((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) * ((A.R : ZMod q) * (w : ZMod q))⁻¹
    with hx
  refine ⟨x.val, ZMod.val_lt x, ?_⟩
  rw [mem_Gamma0_iff, gam_mul_apply_10, hw, hMz]
  have key : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + ((A.R : ℤ) * (x.val : ℕ) + q) * w := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero, hx]
    have hR0 : (A.R : ZMod q) ≠ 0 := left_ne_zero_of_mul hRw
    have hw0 : (w : ZMod q) ≠ 0 := right_ne_zero_of_mul hRw
    field_simp
    ring
  obtain ⟨t, ht⟩ := key
  refine ⟨t, ?_⟩
  linear_combination (A.R : ℤ) * ht

private def tr [NeZero M] (o : Option (Fin q)) :
    ↥((CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ))) :=
  o.elim 1 (fun j => ⟨((gam A ((j : ℕ) : ℤ) : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹,
    inv_mem (Subgroup.mem_map_of_mem _ (gam_mem A _))⟩)

private lemma mapGL_injective : Function.Injective (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) → GL (Fin 2) ℝ) := by
  intro a b h
  have h' := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ)) h
  ext i j
  have := congrFun (congrFun h' i) j
  simpa [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.map_apply_coe] using this

private lemma tr_bijective [NeZero M] (hq : q.Prime) :
    Function.Bijective (fun o : Option (Fin q) =>
      (⟦tr A o⟧ : ↥((CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ))) ⧸
        ((CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))).subgroupOf
          (CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ)))) := by

  have crit : ∀ x y : ↥((CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ))),
      (⟦x⟧ : ↥((CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ))) ⧸
        ((CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))).subgroupOf
          (CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ))) = ⟦y⟧ ↔
      ((x : GL (Fin 2) ℝ)⁻¹ * y ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) := by
    intro x y
    rw [Quotient.eq]
    exact QuotientGroup.leftRel_apply.trans Subgroup.mem_subgroupOf

  have memiff : ∀ (γ : SL(2, ℤ)) (N : ℕ),
      ((γ : GL (Fin 2) ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) ↔
        γ ∈ CongruenceSubgroup.Gamma0 N :=
    fun γ N => Subgroup.mem_map_iff_mem mapGL_injective
  constructor
  · rintro (_ | i) (_ | j) h
    · rfl
    · exfalso
      rw [crit] at h
      simp only [tr, Option.elim, OneMemClass.coe_one, inv_one, one_mul] at h
      rw [← map_inv, ← map_inv, memiff] at h
      exact not_gam_mem A hq _ (inv_mem_iff.mp h)
    · exfalso
      rw [crit] at h
      simp only [tr, Option.elim, OneMemClass.coe_one, mul_one, inv_inv] at h
      rw [memiff] at h
      exact not_gam_mem A hq _ h
    · rw [crit] at h
      simp only [tr, Option.elim, inv_inv] at h
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, memiff, gam_mul_gam_inv_mem_iff A] at h
      congr 1
      ext
      have hi := i.isLt; have hj := j.isLt
      have h' : (((i : ℕ) : ℤ) : ZMod q) = (((j : ℕ) : ℤ) : ZMod q) :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by simpa using h)
      simp only [Int.cast_natCast] at h'
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h'
      rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
      exact this
  · intro c
    induction c using Quotient.inductionOn with
    | h y =>
      obtain ⟨γ, hγ, hγy⟩ := Subgroup.mem_map.mp y.property
      have hγy' : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (y : GL (Fin 2) ℝ) := hγy
      by_cases hγM : γ ∈ CongruenceSubgroup.Gamma0 M
      · refine ⟨none, ?_⟩
        rw [crit]
        simp only [tr, Option.elim, OneMemClass.coe_one, inv_one, one_mul]
        rw [← hγy']
        exact (memiff γ M).mpr hγM
      · obtain ⟨j, hjq, hj⟩ := exists_gam_mul_mem A hq γ hγ hγM
        refine ⟨some ⟨j, hjq⟩, ?_⟩
        rw [crit]
        simp only [tr, Option.elim, inv_inv]
        rw [← hγy', ← map_mul, ← map_mul, memiff]
        exact hj

end TRWAux
p2m_reactivate "P2MW.S_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash.RC1.TRWAux"

end RC1
p2m_reactivate "P2MW.S_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash.RC1.TRWAux P2MW.S_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash.RC1"

open RC1 in

theorem solution (q : ℕ) (hq : q.Prime) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q)
    (k : ℤ) (F : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ G : CuspForm (CongruenceSubgroup.Gamma0 A.R) k,
      ⇑G = ⇑F + (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k ⇑F) := by
  classical
  haveI : NeZero A.R := ⟨A.R_pos.ne'⟩
  haveI hfi : (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.isFiniteRelIndex_of_le_right _ (Subgroup.map_le_range _ _)
  refine ⟨CuspForm.trace (CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ)) F, ?_⟩
  rw [CuspForm.coe_trace, TRWAux.smul_heckeU_alSlash]
  letI : Fintype (↥(CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ)) ⧸
      ((CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))).subgroupOf
        (CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ))) := Fintype.ofFinite _
  refine ((Equiv.sum_comp (Equiv.ofBijective _ (TRWAux.tr_bijective A hq)) _).symm).trans ?_
  rw [Fintype.sum_option]
  simp only [Equiv.ofBijective_apply, TRWAux.tr, Option.elim, SlashInvariantForm.quotientFunc_mk,
    OneMemClass.coe_one, inv_one, SlashAction.slash_one, inv_inv]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun j => (⇑F) ∣[k] ((TRWAux.gam A (j : ℤ) : SL(2, ℤ)) : GL (Fin 2) ℝ)) q

end S_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash
end P2MW
export P2MW.S_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash (solution)
