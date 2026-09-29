-- Prove2me | solution 1 for CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d90051e7-1764-59e6-b641-3f8cedfec6e8

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_AutomorphicForm_ModularFundamentalDomain
import Definitions.Def_CuspForm_PeterssonCoset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter CongruenceSubgroup
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace HeckeBoundGamma1

open CuspForm.PeterssonCoset

section groups

theorem mul_apply' (A B : SL(2, ℤ)) (i j : Fin 2) :
    ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j
      = (A : Matrix (Fin 2) (Fin 2) ℤ) i 0 * (B : Matrix (Fin 2) (Fin 2) ℤ) 0 j
        + (A : Matrix (Fin 2) (Fin 2) ℤ) i 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem intCast_eq_one_iff (M : ℕ) (a : ℤ) : (a : ZMod M) = 1 ↔ (M : ℤ) ∣ a - 1 := by
  rw [show (1 : ZMod M) = ((1 : ℤ) : ZMod M) by norm_cast, ZMod.intCast_eq_intCast_iff_dvd_sub,
    dvd_sub_comm]

def Lam0 (M ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {γ | (M : ℤ) ∣ γ 0 0 - 1 ∧ (M : ℤ) ∣ γ 1 1 - 1 ∧
    ((M / ℓ : ℕ) : ℤ) ∣ γ 0 1 ∧ ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0}
  one_mem' := by simp
  mul_mem' := by
    rintro A B ⟨hA1, hA2, hA3, hA4⟩ ⟨hB1, hB2, hB3, hB4⟩
    have hbc : (M : ℤ) ∣ ((M / ℓ : ℕ) : ℤ) * ((M * ℓ : ℕ) : ℤ) := by
      push_cast; exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (M : ℤ) ∣ (A * B) 0 0 - 1
      rw [mul_apply']
      have : A 0 0 * B 0 0 + A 0 1 * B 1 0 - 1
          = (A 0 0 - 1) * (B 0 0 - 1) + (A 0 0 - 1) + (B 0 0 - 1) + A 0 1 * B 1 0 := by ring
      rw [this]
      exact dvd_add (dvd_add (dvd_add (hA1.mul_right _) hA1) hB1) (hbc.trans (mul_dvd_mul hA3 hB4))
    · show (M : ℤ) ∣ (A * B) 1 1 - 1
      rw [mul_apply']
      have : A 1 0 * B 0 1 + A 1 1 * B 1 1 - 1
          = (A 1 1 - 1) * (B 1 1 - 1) + (A 1 1 - 1) + (B 1 1 - 1) + B 0 1 * A 1 0 := by ring
      rw [this]
      exact dvd_add (dvd_add (dvd_add (hA2.mul_right _) hA2) hB2) (hbc.trans (mul_dvd_mul hB3 hA4))
    · show ((M / ℓ : ℕ) : ℤ) ∣ (A * B) 0 1
      rw [mul_apply']
      exact dvd_add (hB3.mul_left _) (hA3.mul_right _)
    · show ((M * ℓ : ℕ) : ℤ) ∣ (A * B) 1 0
      rw [mul_apply']
      exact dvd_add (hA4.mul_right _) (hB4.mul_left _)
  inv_mem' := by
    rintro A ⟨hA1, hA2, hA3, hA4⟩
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, dvd_neg]
    exact ⟨hA2, hA1, hA3, hA4⟩

variable {M ℓ : ℕ}

theorem mem_Lam0 {γ : SL(2, ℤ)} : γ ∈ Lam0 M ℓ ↔ (M : ℤ) ∣ γ 0 0 - 1 ∧ (M : ℤ) ∣ γ 1 1 - 1 ∧
    ((M / ℓ : ℕ) : ℤ) ∣ γ 0 1 ∧ ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 := Iff.rfl

theorem Lam0_le_Gamma1 : Lam0 M ℓ ≤ Gamma1 M := by
  rintro γ ⟨h1, h2, -, h4⟩
  rw [Gamma1_mem]
  refine ⟨(intCast_eq_one_iff M _).mpr h1, (intCast_eq_one_iff M _).mpr h2, ?_⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (by push_cast; exact dvd_mul_right _ _ : (M : ℤ) ∣ ((M * ℓ : ℕ) : ℤ)).trans h4

theorem Gamma_le_Lam0 (hℓM : ℓ ∣ M) : Gamma (M * ℓ) ≤ Lam0 M ℓ := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  have hM : (M : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) := by push_cast; exact dvd_mul_right _ _
  have hMl : ((M / ℓ : ℕ) : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr ((Nat.div_dvd_of_dvd hℓM).trans (dvd_mul_right M ℓ))
  refine ⟨hM.trans ((intCast_eq_one_iff _ _).mp h00), hM.trans ((intCast_eq_one_iff _ _).mp h11),
    hMl.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10⟩

theorem Gamma_le_Gamma1 : Gamma M ≤ Gamma1 M := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

theorem Gamma1_le_of_dvd {N : ℕ} (h : M ∣ N) : Gamma1 N ≤ Gamma1 M := by
  intro γ hγ
  rw [Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have hMN : (M : ℤ) ∣ N := Int.natCast_dvd_natCast.mpr h
  refine ⟨(intCast_eq_one_iff M _).mpr (hMN.trans ((intCast_eq_one_iff N _).mp h1)),
    (intCast_eq_one_iff M _).mpr (hMN.trans ((intCast_eq_one_iff N _).mp h2)), ?_⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3 ⊢
  exact hMN.trans h3

scoped instance Lam0_finiteIndex [NeZero M] [hl : Fact ℓ.Prime] [hd : Fact (ℓ ∣ M)] : (Lam0 M ℓ).FiniteIndex := by
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) hl.out.ne_zero⟩
  have hcong : IsCongruenceSubgroup (Lam0 M ℓ) := ⟨M * ℓ, NeZero.ne _, Gamma_le_Lam0 hd.out⟩
  exact hcong.finiteIndex

scoped instance fintypeQuotLam0 [NeZero M] [Fact ℓ.Prime] [Fact (ℓ ∣ M)] : Fintype (SL(2, ℤ) ⧸ Lam0 M ℓ) :=
  haveI : Finite (SL(2, ℤ) ⧸ Lam0 M ℓ) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

scoped instance fintypeQuotGamma [NeZero M] : Fintype (SL(2, ℤ) ⧸ Gamma M) :=
  haveI : Finite (SL(2, ℤ) ⧸ Gamma M) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

scoped instance fintypeQuotGamma1 [NeZero M] : Fintype (SL(2, ℤ) ⧸ Gamma1 M) :=
  haveI : Finite (SL(2, ℤ) ⧸ Gamma1 M) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

def dConjMat (ℓ : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0, ℓ * γ 0 1; γ 1 0 / ℓ, γ 1 1]

def dConjInvMat (ℓ : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0, γ 0 1 / ℓ; ℓ * γ 1 0, γ 1 1]

theorem det_dConjMat {γ : SL(2, ℤ)} (h : (ℓ : ℤ) ∣ γ 1 0) : (dConjMat ℓ γ).det = 1 := by
  rw [dConjMat, Matrix.det_fin_two_of]
  have e := Int.mul_ediv_cancel' h
  linear_combination det_entries γ - (γ 0 1) * e

theorem det_dConjInvMat {γ : SL(2, ℤ)} (h : (ℓ : ℤ) ∣ γ 0 1) : (dConjInvMat ℓ γ).det = 1 := by
  rw [dConjInvMat, Matrix.det_fin_two_of]
  have e := Int.mul_ediv_cancel' h
  linear_combination det_entries γ - (γ 1 0) * e

theorem dvd_10_of_mem_Lam0 {γ : SL(2, ℤ)} (hγ : γ ∈ Lam0 M ℓ) : (ℓ : ℤ) ∣ γ 1 0 :=
  (by push_cast; exact dvd_mul_left _ _ : (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ)).trans hγ.2.2.2

theorem dvd_01_of_mem_Gamma (hℓM : ℓ ∣ M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma M) : (ℓ : ℤ) ∣ γ 0 1 :=
  (Int.natCast_dvd_natCast.mpr hℓM).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma_mem.mp hγ).2.1)

def dConj (hℓM : ℓ ∣ M) (γ : Lam0 M ℓ) : Gamma M :=
  ⟨⟨dConjMat ℓ γ, det_dConjMat (dvd_10_of_mem_Lam0 γ.2)⟩, by
    obtain ⟨h1, h2, h3, h4⟩ := γ.2
    rw [Gamma_mem]
    simp only [dConjMat, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ⟨(intCast_eq_one_iff M _).mpr h1, ?_, ?_, (intCast_eq_one_iff M _).mpr h2⟩
    · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      obtain ⟨t, ht⟩ := h3
      rw [ht, ← mul_assoc]
      refine Dvd.dvd.mul_right ?_ _
      exact ⟨1, by exact_mod_cast (by rw [mul_one, Nat.mul_div_cancel' hℓM] : ℓ * (M / ℓ) = M * 1)⟩
    · rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      obtain ⟨t, ht⟩ := h4
      have hℓ0 : (ℓ : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := dvd_10_of_mem_Lam0 γ.2
      rcases eq_or_ne ℓ 0 with hz | hz
      · subst hz
        simp only [Nat.cast_zero, Int.ediv_zero]
        exact dvd_zero _
      have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hz
      have : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (ℓ : ℤ) = M * t := by
        apply mul_left_cancel₀ hℓ'
        rw [Int.mul_ediv_cancel' hℓ0, ht]; push_cast; ring
      rw [this]; exact dvd_mul_right _ _⟩

def dConjInv (hℓM : ℓ ∣ M) (γ : Gamma M) : Lam0 M ℓ :=
  ⟨⟨dConjInvMat ℓ γ, det_dConjInvMat (dvd_01_of_mem_Gamma hℓM γ.2)⟩, by
    have hγ := Gamma_mem.mp γ.2
    obtain ⟨h1, h2, h3, h4⟩ := hγ
    simp only [mem_Lam0, dConjInvMat, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    refine ⟨(intCast_eq_one_iff M _).mp h1, (intCast_eq_one_iff M _).mp h4, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
      rcases eq_or_ne ℓ 0 with hz | hz
      · subst hz; simp
      have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hz
      have : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / (ℓ : ℤ) = (M / ℓ : ℕ) * t := by
        apply mul_left_cancel₀ hℓ'
        rw [Int.mul_ediv_cancel' (dvd_01_of_mem_Gamma hℓM γ.2), ht,
          show (M : ℤ) = (M / ℓ : ℕ) * ℓ by exact_mod_cast (Nat.div_mul_cancel hℓM).symm]
        ring
      rw [this]; exact dvd_mul_right _ _
    · obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h3
      rw [ht]; push_cast
      exact ⟨t, by ring⟩⟩

theorem heckeDiag_mul_eq (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (γ : Lam0 M ℓ) :
    heckeDiagMatrix ℓ * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((dConj hℓM γ : Gamma M) : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * heckeDiagMatrix ℓ := by
  have e := Int.mul_ediv_cancel' (dvd_10_of_mem_Lam0 (M := M) (ℓ := ℓ) γ.2)
  have e' : (ℓ : ℝ) * ((((γ : SL(2, ℤ)) 1 0 / (ℓ : ℤ) : ℤ) : ℝ)) = ((γ : SL(2, ℤ)) 1 0 : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) e
    simpa only [Int.cast_mul, Int.cast_natCast] using h
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix hℓ, val_mapGL_eq, val_mapGL_eq]
  simp only [dConj, Matrix.SpecialLinearGroup.coe_mk, dConjMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals first | ring1 | (linear_combination e') | (linear_combination -e')

theorem heckeDiag_mul_eq' (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (γ : Gamma M) :
    (heckeDiagMatrix ℓ)⁻¹ * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((dConjInv hℓM γ : Lam0 M ℓ) : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * (heckeDiagMatrix ℓ)⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
  have e := Int.mul_ediv_cancel' (dvd_01_of_mem_Gamma hℓM γ.2)
  have e' : (ℓ : ℝ) * ((((γ : SL(2, ℤ)) 0 1 / (ℓ : ℤ) : ℤ) : ℝ)) = ((γ : SL(2, ℤ)) 0 1 : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) e
    simpa only [Int.cast_mul, Int.cast_natCast] using h
  symm
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix hℓ, val_mapGL_eq, val_mapGL_eq]
  simp only [dConjInv, Matrix.SpecialLinearGroup.coe_mk, dConjInvMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals first | ring1 | (linear_combination e')

theorem delta_mul_eq (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (γ : Gamma M) :
    heckeMatrix ℓ 0 * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((dConjInv hℓM γ : Lam0 M ℓ) : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * heckeMatrix ℓ 0 := by
  have e := Int.mul_ediv_cancel' (dvd_01_of_mem_Gamma hℓM γ.2)
  have e' : (ℓ : ℝ) * ((((γ : SL(2, ℤ)) 0 1 / (ℓ : ℤ) : ℤ) : ℝ)) = ((γ : SL(2, ℤ)) 0 1 : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) e
    simpa only [Int.cast_mul, Int.cast_natCast] using h
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeMatrix hℓ, val_mapGL_eq, val_mapGL_eq]
  simp only [dConjInv, Matrix.SpecialLinearGroup.coe_mk, dConjInvMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals first | ring1 | (linear_combination e') | (linear_combination -e')

theorem mapGL_dConj (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (γ : Lam0 M ℓ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ((dConj hℓM γ : Gamma M) : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = heckeDiagMatrix ℓ * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * (heckeDiagMatrix ℓ)⁻¹ := by
  rw [heckeDiag_mul_eq hℓM hℓ γ, mul_inv_cancel_right]

theorem mapGL_dConjInv (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (γ : Gamma M) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ((dConjInv hℓM γ : Lam0 M ℓ) : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (heckeDiagMatrix ℓ)⁻¹ * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * heckeDiagMatrix ℓ := by
  rw [heckeDiag_mul_eq' hℓM hℓ γ, inv_mul_cancel_right]

def dInvEquiv (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) : Gamma M ≃ Lam0 M ℓ where
  toFun := dConjInv hℓM
  invFun := dConj hℓM
  left_inv γ := by
    apply Subtype.ext
    apply mapGL_injective
    show (Matrix.SpecialLinearGroup.mapGL ℝ ((dConj hℓM (dConjInv hℓM γ) : Gamma M) : SL(2, ℤ)) : GL (Fin 2) ℝ) = _
    rw [mapGL_dConj hℓM hℓ, mapGL_dConjInv hℓM hℓ]; group
  right_inv γ := by
    apply Subtype.ext
    apply mapGL_injective
    show (Matrix.SpecialLinearGroup.mapGL ℝ ((dConjInv hℓM (dConj hℓM γ) : Lam0 M ℓ) : SL(2, ℤ)) : GL (Fin 2) ℝ) = _
    rw [mapGL_dConjInv hℓM hℓ, mapGL_dConj hℓM hℓ]; group

theorem dInvEquiv_spec (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (γ : Gamma M) :
    heckeMatrix ℓ 0 * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((dInvEquiv hℓM hℓ γ : Lam0 M ℓ) : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * heckeMatrix ℓ 0 :=
  delta_mul_eq hℓM hℓ γ

def conjEquiv (N : ℕ) (σ : SL(2, ℤ)) : Gamma N ≃ Gamma N where
  toFun γ := ⟨σ * γ * σ⁻¹, (Gamma_normal N).conj_mem _ γ.2 σ⟩
  invFun γ := ⟨σ⁻¹ * γ * σ⁻¹⁻¹, (Gamma_normal N).conj_mem _ γ.2 σ⁻¹⟩
  left_inv γ := by
    apply Subtype.ext
    show σ⁻¹ * (σ * γ * σ⁻¹) * σ⁻¹⁻¹ = γ
    group
  right_inv γ := by
    apply Subtype.ext
    show σ * (σ⁻¹ * γ * σ⁻¹⁻¹) * σ⁻¹ = γ
    group

theorem conjEquiv_spec (N : ℕ) (σ : SL(2, ℤ)) (γ : Gamma N) :
    (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
        * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((conjEquiv N σ γ : Gamma N) : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) := by
  show _ = (Matrix.SpecialLinearGroup.mapGL ℝ (σ * (γ : SL(2, ℤ)) * σ⁻¹) : GL (Fin 2) ℝ) * _
  rw [map_mul, map_mul, map_inv, inv_mul_cancel_right]

theorem det_mapGL (σ : SL(2, ℤ)) :
    (((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ).det : ℝ)) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_mapGL_eq, Matrix.det_fin_two_of]
  have h := det_entries σ
  exact_mod_cast h

theorem coe_T_pow (j : ℕ) :
    ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![(1 : ℤ), (j : ℤ); 0, 1] := by
  rw [← zpow_natCast]
  exact ModularGroup.coe_T_zpow (j : ℤ)

theorem heckeMatrix_eq_delta_mul (hℓ : ℓ ≠ 0) (j : ℕ) :
    heckeMatrix ℓ j = heckeMatrix ℓ 0
      * (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ j) : GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [Units.val_mul, val_heckeMatrix hℓ, val_heckeMatrix hℓ, val_mapGL_eq]
  have hT : ∀ i i', ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i i'
      = (!![(1 : ℤ), (j : ℤ); 0, 1]) i i' := fun i i' => by rw [coe_T_pow]
  have h00 : ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by rw [hT]; simp
  have h01 : ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = j := by rw [hT]; simp
  have h10 : ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by rw [hT]; simp
  have h11 : ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by rw [hT]; simp
  rw [h00, h01, h10, h11]
  simp only [Matrix.mul_fin_two]
  ext i i'
  fin_cases i <;> fin_cases i' <;> simp

def gam0 (M ℓ : ℕ) (u v : ℤ) (h : u * ℓ + v * M = 1) : SL(2, ℤ) :=
  ⟨!![u, -v; (M : ℤ), (ℓ : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

def sig0 (M ℓ : ℕ) (u v : ℤ) (h : u * ℓ + v * M = 1) : SL(2, ℤ) :=
  ⟨!![(ℓ : ℤ) * u, -v; (M : ℤ), 1], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

theorem gam0_mem (u v : ℤ) (h : u * ℓ + v * M = 1) : gam0 M ℓ u v h ∈ Gamma0 M := by
  rw [Gamma0_mem]
  show ((((!![u, -v; (M : ℤ), (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) : ZMod M) = 0
  simp

theorem gam0_apply_11 (u v : ℤ) (h : u * ℓ + v * M = 1) : (gam0 M ℓ u v h) 1 1 = (ℓ : ℤ) := by
  show (!![u, -v; (M : ℤ), (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ℓ
  simp

theorem gam0_mul_heckeDiag (hℓ : ℓ ≠ 0) (u v : ℤ) (h : u * ℓ + v * M = 1) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (gam0 M ℓ u v h) : GL (Fin 2) ℝ) * heckeDiagMatrix ℓ
      = heckeMatrix ℓ 0 * (Matrix.SpecialLinearGroup.mapGL ℝ (sig0 M ℓ u v h) : GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix hℓ, val_heckeMatrix hℓ, val_mapGL_eq, val_mapGL_eq]
  simp only [gam0, sig0, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

end groups

section qexp

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ} {p : ℕ}

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁(M)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem hasSum_F (F : CuspForm Γ₁(M) k) (z : ℍ) :
    HasSum (fun n : ℕ => (qExpansion 1 F).coeff n • Function.Periodic.qParam 1 (z : ℂ) ^ n) (F z) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁(M))) :=
    ⟨(Γ₁(M)).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  exact UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods M))
    (CuspForm.holo' F) (ModularFormClass.bdd_at_infty F) z

theorem qParam_heckeMatrix_smul (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((heckeMatrix p j • τ : ℍ) : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * τ / p) * Complex.exp (2 * Real.pi * Complex.I / p) ^ j := by
  rw [coe_heckeMatrix_smul hp j τ, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  field_simp

theorem r_pow_mul (hp : p ≠ 0) (τ : ℍ) (m : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * τ / p) ^ (p * m) = Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  field_simp

theorem qParam_heckeDiag_smul (hp : p ≠ 0) (τ : ℍ) :
    Function.Periodic.qParam 1 ((heckeDiagMatrix p • τ : ℍ) : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ p := by
  rw [coe_heckeDiagMatrix_smul hp, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem geom_sum_root (hp : p ≠ 0) (n : ℕ) :
    ∑ u ∈ Finset.range p, (Complex.exp (2 * Real.pi * Complex.I / p) ^ u) ^ n
      = if p ∣ n then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp
  set ζ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hx : ∀ u : ℕ, (ζ ^ u) ^ n = (ζ ^ n) ^ u := fun u => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [hx]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd n).mpr h]
    simp
  · have hne : ζ ^ n ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd n).mp h1)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem sum_apply_heckeMatrix_smul (hp : p ≠ 0) (F : CuspForm Γ₁(M) k) (e a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff F (p * n)
      + e * (if p ∣ n then ModularFormClass.qCoeff F (n / p) else 0) = a * ModularFormClass.qCoeff F n)
    (τ : ℍ) :
    ∑ j ∈ Finset.range p, F (heckeMatrix p j • τ)
      = (p : ℂ) * (a * F τ - e * F (heckeDiagMatrix p • τ)) := by
  set c : ℕ → ℂ := fun n => (qExpansion 1 F).coeff n with hc
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hq
  set r := Complex.exp (2 * Real.pi * Complex.I * τ / p) with hr
  set ζ := Complex.exp (2 * Real.pi * Complex.I / p) with hζ
  have ha' : ∀ m : ℕ, c (p * m) = a * c m - e * (if p ∣ m then c (m / p) else 0) := fun m => by
    have h := ha m
    simp only [ModularFormClass.qCoeff] at h
    linear_combination h

  set g : ℕ → ℂ := fun n => (if p ∣ n then (p : ℂ) else 0) * (c n * r ^ n) with hg

  have h1 : HasSum g (∑ j ∈ Finset.range p, F (heckeMatrix p j • τ)) := by
    have hu : ∀ j ∈ Finset.range p,
        HasSum (fun n : ℕ => c n * (r ^ n * (ζ ^ j) ^ n)) (F (heckeMatrix p j • τ)) := by
      intro j _
      have h := hasSum_F F (heckeMatrix p j • τ)
      simp only [qParam_heckeMatrix_smul hp j τ, smul_eq_mul, mul_pow] at h
      exact h
    have hs := hasSum_sum hu
    refine hs.congr_fun fun n => ?_
    show (if p ∣ n then (p : ℂ) else 0) * (c n * r ^ n) = ∑ i ∈ Finset.range p, c n * (r ^ n * (ζ ^ i) ^ n)
    have : ∀ i : ℕ, c n * (r ^ n * (ζ ^ i) ^ n) = (c n * r ^ n) * (ζ ^ i) ^ n := fun i => by ring
    simp only [this]
    rw [← Finset.mul_sum, geom_sum_root hp n]
    ring

  have hF : HasSum (fun m : ℕ => c m * q ^ m) (F τ) := by
    have h := hasSum_F F τ
    simp only [smul_eq_mul] at h
    exact h
  set G : ℕ → ℂ := fun m => (if p ∣ m then c (m / p) else 0) * q ^ m with hG
  have hGD : HasSum G (F (heckeDiagMatrix p • τ)) := by
    have h := hasSum_F F (heckeDiagMatrix p • τ)
    simp only [qParam_heckeDiag_smul hp τ, smul_eq_mul] at h
    have h' : HasSum (fun m : ℕ => G (p * m)) (F (heckeDiagMatrix p • τ)) := by
      refine h.congr_fun fun m => ?_
      show (if p ∣ p * m then c (p * m / p) else 0) * q ^ (p * m) = c m * (q ^ p) ^ m
      rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hp), pow_mul]
    refine (Function.Injective.hasSum_iff (mul_right_injective₀ hp) ?_).mp h'
    intro x hx
    have hnd : ¬ p ∣ x := fun ⟨m, hm⟩ => hx ⟨m, hm.symm⟩
    simp only [hG, if_neg hnd, zero_mul]
  have h2 : HasSum (fun m : ℕ => g (p * m)) ((p : ℂ) * (a * F τ - e * F (heckeDiagMatrix p • τ))) := by
    have h := (hF.mul_left ((p : ℂ) * a)).sub (hGD.mul_left ((p : ℂ) * e))
    have hval : (p : ℂ) * a * F τ - (p : ℂ) * e * F (heckeDiagMatrix p • τ)
        = (p : ℂ) * (a * F τ - e * F (heckeDiagMatrix p • τ)) := by ring
    rw [hval] at h
    refine h.congr_fun fun m => ?_
    have hrq : r ^ (p * m) = q ^ m := by rw [hr, hq]; exact r_pow_mul hp τ m
    show g (p * m) = (p : ℂ) * a * (c m * q ^ m) - (p : ℂ) * e * G m
    simp only [hg, hG, if_pos (dvd_mul_right p m), ha' m]
    rw [hrq]
    ring

  have h3 : HasSum g ((p : ℂ) * (a * F τ - e * F (heckeDiagMatrix p • τ))) := by
    refine (Function.Injective.hasSum_iff (mul_right_injective₀ hp) ?_).mp h2
    intro x hx
    have hnd : ¬ p ∣ x := fun ⟨m, hm⟩ => hx ⟨m, hm.symm⟩
    simp only [hg, if_neg hnd, zero_mul]
  exact h1.unique h3

theorem heckeT_eq_smul (hp : p ≠ 0) (F : CuspForm Γ₁(M) k) (e₀ a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff F (p * n)
      + e₀ * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff F (n / p) else 0)
        = a * ModularFormClass.qCoeff F n) :
    heckeU k p ⇑F + e₀ • ((⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix p) = a • (⇑F : ℍ → ℂ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  funext τ
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, heckeU_apply k hp,
    slash_heckeDiagMatrix_apply k hp,
    sum_apply_heckeMatrix_smul hp F (e₀ * (p : ℂ) ^ (k - 1)) a (fun n => by rw [← ha n]) τ]
  field_simp
  ring

end qexp

section nice

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ}

theorem dens_slash {β : GL (Fin 2) ℝ} (hβ : 0 < (β.det : ℝ)) (F : ℍ → ℂ) (x : ℍ) :
    dens k (F ∣[k] β) x = (β.det : ℝ) ^ (k - 2) * dens k F (β • x) := by
  have h := UpperHalfPlane.petersson_slash k F F β x
  rw [UpperHalfPlane.σ, if_pos hβ, abs_of_pos hβ, petersson_self_eq_dens, petersson_self_eq_dens] at h
  simp only [ContinuousAlgEquiv.refl_apply] at h
  exact_mod_cast h

theorem nice_cuspForm [NeZero M] (F : CuspForm Γ₁(M) k) : Nice (Gamma1 M) k ⇑F := by
  refine ⟨F.holo'.continuous, ?_, fun h hh => SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hh)⟩
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ₁(M) F F
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rwa [petersson_self_eq_dens, Complex.norm_real, Real.norm_of_nonneg (dens_nonneg k _ x)] at this

theorem nice_slash_of_conj [NeZero M] {Λ₁ Λ : Subgroup SL(2, ℤ)} (β : GL (Fin 2) ℝ)
    (hβ : 0 < (β.det : ℝ)) (c : Λ₁ → Λ)
    (hc : ∀ h : Λ₁, β * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((c h : Λ) : SL(2, ℤ)) : GL (Fin 2) ℝ) * β)
    (hΛ : Λ ≤ Gamma1 M) (F : CuspForm Γ₁(M) k) :
    Nice Λ₁ k ((⇑F : ℍ → ℂ) ∣[k] β) := by
  have hF := nice_cuspForm F
  obtain ⟨C, hC⟩ := hF.bdd
  refine ⟨(F.holo'.slash k β).continuous, ⟨(β.det : ℝ) ^ (k - 2) * C, fun x => ?_⟩, fun h hh => ?_⟩
  · rw [dens_slash hβ]
    exact mul_le_mul_of_nonneg_left (hC _) (zpow_nonneg hβ.le _)
  · rw [← SlashAction.slash_mul, hc ⟨h, hh⟩, SlashAction.slash_mul, hF.inv _ (hΛ (c ⟨h, hh⟩).2)]

theorem slash_eq_smul_of_hasNebentypus {ε : DirichletCharacter ℂ M} {g : CuspForm Γ₁(M) k}
    (hg : CuspForm.HasNebentypus ε g) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε ((γ 1 1 : ℤ) : ZMod M) • (⇑g : ℍ → ℂ) := by
  funext τ
  have h := ModularForm.SL_slash_apply (f := ⇑g) (k := k) γ τ
  rw [ModularGroup.denom_apply] at h
  rw [show ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
      = ((⇑g : ℍ → ℂ) ∣[k] γ) τ from rfl, h, hg γ hγ τ, Pi.smul_apply, smul_eq_mul]
  have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) τ
    rwa [show denom (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) τ
      = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) from ModularGroup.denom_apply γ τ] at this
  have hk : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k ≠ 0 := zpow_ne_zero k hne
  rw [zpow_neg]
  field_simp

end nice

section pairalg

variable (Λ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ)] {k : ℤ}

theorem pair_self_ofReal {G : ℍ → ℂ} (hG : Continuous G) :
    pair Λ k G G = (((pair Λ k G G).re : ℝ) : ℂ) ∧ 0 ≤ (pair Λ k G G).re := by
  rw [pair_self_eq_lintegral Λ (k := k) hG]
  refine ⟨by simp, ?_⟩
  simp only [Complex.ofReal_re]
  exact ENNReal.toReal_nonneg

theorem pair_zero_right (F : ℍ → ℂ) : pair Λ k F 0 = 0 := by
  have h := pair_smul_right Λ (k := k) 0 F 0
  rwa [zero_smul, zero_mul] at h

theorem pair_add_left' {u v w : ℍ → ℂ} (hu : Nice Λ k u) (hv : Nice Λ k v) (hw : Nice Λ k w) :
    pair Λ k (u + v) w = pair Λ k u w + pair Λ k v w := by
  have h := pair_sum_left Λ (k := k) Finset.univ ![u, v] w
    (fun i => by fin_cases i <;> assumption) hw
  simpa [Fin.sum_univ_two] using h

theorem pair_neg_left' (u w : ℍ → ℂ) : pair Λ k (-u) w = -pair Λ k u w := by
  have h := pair_smul_left Λ (k := k) (-1) u w
  rwa [neg_one_smul, map_neg, map_one, neg_one_mul] at h

theorem pair_sub_left' {u v w : ℍ → ℂ} (hu : Nice Λ k u) (hv : Nice Λ k v) (hw : Nice Λ k w) :
    pair Λ k (u - v) w = pair Λ k u w - pair Λ k v w := by
  rw [sub_eq_add_neg, pair_add_left' Λ hu hv.neg hw, pair_neg_left', ← sub_eq_add_neg]

theorem pair_sub_right' {u v w : ℍ → ℂ} (hu : Nice Λ k u) (hv : Nice Λ k v) (hw : Nice Λ k w) :
    pair Λ k w (u - v) = pair Λ k w u - pair Λ k w v := by
  rw [pair_conj_symm Λ (u - v) w, pair_sub_left' Λ hu hv hw, map_sub, ← pair_conj_symm Λ u w,
    ← pair_conj_symm Λ v w]

theorem norm_pair_sq_le {u v : ℍ → ℂ} (hu : Nice Λ k u) (hv : Nice Λ k v) :
    ‖pair Λ k u v‖ ^ 2 ≤ (pair Λ k u u).re * (pair Λ k v v).re := by
  obtain ⟨hvre, hvnn⟩ := pair_self_ofReal Λ (k := k) hv.cont
  obtain ⟨hure, hunn⟩ := pair_self_ofReal Λ (k := k) hu.cont
  set Pv : ℝ := (pair Λ k v v).re with hPv
  by_cases hP : Pv = 0
  · have hv0 : v = 0 := eq_zero_of_pair_self_eq_zero Λ hv (by rw [hvre, hP]; simp)
    rw [hv0, pair_zero_right, norm_zero, hP]
    simp
  · have hPpos : 0 < Pv := lt_of_le_of_ne hvnn (Ne.symm hP)
    set z : ℂ := pair Λ k v u with hz
    have hzuv : pair Λ k u v = conj z := pair_conj_symm Λ v u
    set t : ℂ := z / (Pv : ℂ) with ht
    have htv : Nice Λ k (t • v) := hv.smul t
    have hw : Nice Λ k (u - t • v) := hu.sub htv
    obtain ⟨hwre, hwnn⟩ := pair_self_ofReal Λ (k := k) hw.cont
    have hPc : (Pv : ℂ) ≠ 0 := by exact_mod_cast hP
    have hexp : pair Λ k (u - t • v) (u - t • v) = pair Λ k u u - z * conj z / (Pv : ℂ) := by
      rw [pair_sub_left' Λ hu htv hw, pair_sub_right' Λ hu htv hu, pair_sub_right' Λ hu htv htv,
        pair_smul_right, pair_smul_left, pair_smul_left, pair_smul_right, hzuv, hvre, ← hz, ht,
        map_div₀, Complex.conj_ofReal]
      field_simp
      ring
    have hre : (pair Λ k (u - t • v) (u - t • v)).re = (pair Λ k u u).re - ‖z‖ ^ 2 / Pv := by
      rw [hexp, Complex.sub_re, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_div,
        Complex.ofReal_re]
    have h1 : ‖z‖ ^ 2 / Pv ≤ (pair Λ k u u).re := by linarith [hwnn]
    rw [hzuv, Complex.norm_conj]
    rwa [div_le_iff₀ hPpos] at h1

end pairalg

section decay

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ} {p : ℕ}

theorem im_heckeDiag_smul (hp : p ≠ 0) (σ : ℍ) : (heckeDiagMatrix p • σ).im = p * σ.im := by
  have h := congrArg Complex.im (coe_heckeDiagMatrix_smul hp σ)
  rw [UpperHalfPlane.coe_im] at h
  rw [h]
  simp [Complex.mul_im]

theorem heckeMatrix_smul_heckeDiag_smul (hp : p ≠ 0) (σ : ℍ) :
    heckeMatrix p 0 • (heckeDiagMatrix p • σ) = σ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeMatrix_smul hp 0, coe_heckeDiagMatrix_smul hp]
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  push_cast
  field_simp
  ring

theorem eq_zero_of_slash_delta_eq [NeZero M] (hp : p.Prime) (F : CuspForm Γ₁(M) k) {e : ℂ}
    (he : ‖e‖ = 1)
    (h : (⇑F : ℍ → ℂ) ∣[k] heckeMatrix p 0 = e • ((⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix p)) :
    F = 0 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set ψ : ℍ → ℍ := fun σ => heckeDiagMatrix p • (heckeDiagMatrix p • σ) with hψ

  have hpt : ∀ σ : ℍ, ‖F σ‖ = (p : ℝ) ^ k * ‖F (ψ σ)‖ := by
    intro σ
    have h1 := congrFun h (heckeDiagMatrix p • σ)
    rw [slash_heckeMatrix_apply k hp0, heckeMatrix_smul_heckeDiag_smul hp0, Pi.smul_apply, smul_eq_mul,
      slash_heckeDiagMatrix_apply k hp0] at h1
    have h2 := congrArg (fun z : ℂ => ‖z‖) h1
    simp only [norm_mul, norm_inv, Complex.norm_natCast, he, one_mul, Complex.norm_zpow] at h2
    have h3 : ‖F σ‖ = (p : ℝ) * ((p : ℝ) ^ (k - 1) * ‖F (ψ σ)‖) := by
      rw [← h2, ← mul_assoc, mul_inv_cancel₀ hpR.ne', one_mul]
    rw [h3, ← mul_assoc]
    congr 1
    rw [mul_comm, ← zpow_add_one₀ hpR.ne', sub_add_cancel]
  have him : ∀ σ : ℍ, (ψ σ).im = (p : ℝ) ^ 2 * σ.im := by
    intro σ
    simp only [hψ, im_heckeDiag_smul hp0]
    ring

  have hdens : ∀ σ : ℍ, dens k ⇑F (ψ σ) = dens k ⇑F σ := by
    intro σ
    unfold dens
    rw [him σ, hpt σ]
    have hpk : (p : ℝ) ^ k ≠ 0 := zpow_ne_zero k hpR.ne'
    rw [mul_zpow, show ((p : ℝ) ^ 2) ^ k = (p : ℝ) ^ k * (p : ℝ) ^ k by
      rw [← mul_zpow, sq]]
    field_simp
  have hiter : ∀ (n : ℕ) (σ : ℍ), dens k ⇑F (ψ^[n] σ) = dens k ⇑F σ ∧
      (ψ^[n] σ).im = ((p : ℝ) ^ 2) ^ n * σ.im := by
    intro n
    induction n with
    | zero => intro σ; simp
    | succ n ih =>
      intro σ
      rw [Function.iterate_succ_apply', hdens, him, (ih σ).1, (ih σ).2, pow_succ]
      exact ⟨rfl, by ring⟩

  haveI : Fact (IsCusp OnePoint.infty (Γ₁(M))) :=
    ⟨(Γ₁(M)).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  have hZ : IsZeroAtImInfty (UpperHalfPlane.petersson k ⇑F ⇑F) :=
    UpperHalfPlane.IsZeroAtImInfty.petersson_isZeroAtImInfty_left k Γ₁(M)
      (CuspFormClass.zero_at_infty F) F
  have hZ' : Tendsto (UpperHalfPlane.petersson k ⇑F ⇑F) atImInfty (nhds 0) := hZ

  have hall : ∀ σ : ℍ, F σ = 0 := by
    intro σ
    have hseq : Tendsto (fun n : ℕ => ψ^[n] σ) atTop atImInfty := by
      rw [atImInfty, Filter.tendsto_comap_iff]
      have : (UpperHalfPlane.im ∘ fun n : ℕ => ψ^[n] σ) = fun n : ℕ => ((p : ℝ) ^ 2) ^ n * σ.im := by
        funext n; exact (hiter n σ).2
      rw [this]
      have h1 : (1 : ℝ) < (p : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        nlinarith
      exact (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const σ.im_pos
    have hlim := hZ'.comp hseq
    have hconst : (UpperHalfPlane.petersson k ⇑F ⇑F ∘ fun n : ℕ => ψ^[n] σ)
        = fun _ => ((dens k ⇑F σ : ℝ) : ℂ) := by
      funext n
      simp only [Function.comp_apply, petersson_self_eq_dens, (hiter n σ).1]
    rw [hconst] at hlim
    have h0 : ((dens k ⇑F σ : ℝ) : ℂ) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
    have h0' : dens k ⇑F σ = 0 := by exact_mod_cast h0
    unfold dens at h0'
    have hy : 0 < σ.im ^ k := zpow_pos σ.im_pos _
    have : ‖F σ‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h0' with h | h
      · exact h
      · exact absurd h hy.ne'
    simpa using this
  exact DFunLike.ext F 0 fun σ => by simpa using hall σ

end decay

section main

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ} {p : ℕ}

theorem norm_sq_lt [NeZero M] (ε : DirichletCharacter ℂ M) (F : CuspForm Γ₁(M) k) (hF0 : F ≠ 0)
    (hFneb : CuspForm.HasNebentypus ε F) (hp : p.Prime) (hpM : ¬ p ∣ M) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff F (p * n)
      + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff F (n / p) else 0)
        = a * ModularFormClass.qCoeff F n) :
    ‖a‖ ^ 2 < ((p : ℝ) + 1) ^ 2 * (p : ℝ) ^ (k - 2) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp0⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (p ∣ M * p) := ⟨dvd_mul_left p M⟩
  have hpMp : p ∣ M * p := dvd_mul_left p M

  have hΛ₀le : Lam0 (M * p) p ≤ Gamma1 M :=
    (Lam0_le_Gamma1 (M := M * p) (ℓ := p)).trans (Gamma1_le_of_dvd (dvd_mul_right M p))
  have hΓle : Gamma (M * p) ≤ Gamma1 M :=
    (Gamma_le_Gamma1 (M := M * p)).trans (Gamma1_le_of_dvd (dvd_mul_right M p))

  have niceF := nice_cuspForm F
  have niceFΛ : Nice (Lam0 (M * p) p) k ⇑F := niceF.mono hΛ₀le
  have niceFΓ : Nice (Gamma (M * p)) k ⇑F := niceF.mono hΓle

  have hεu : IsUnit (p : ZMod M) := ZMod.isUnit_prime_of_not_dvd hp hpM
  have hεnorm : ‖ε (p : ZMod M)‖ = 1 := by
    have h1 := ε.unit_norm_eq_one hεu.unit
    rwa [IsUnit.unit_spec] at h1

  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (M : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
  have huv' : u * p + v * M = 1 := by linear_combination huv

  set δ : GL (Fin 2) ℝ := heckeMatrix p 0 with hδ
  let sM : ℕ → SL(2, ℤ) := fun j => if j < p then ModularGroup.T ^ j else sig0 M p u v huv'
  let w : ℕ → ℍ → ℂ := fun j =>
    (⇑F : ℍ → ℂ) ∣[k] (δ * (Matrix.SpecialLinearGroup.mapGL ℝ (sM j) : GL (Fin 2) ℝ))
  set v₀ : ℍ → ℂ := (⇑F : ℍ → ℂ) ∣[k] δ with hv₀
  have hwj : ∀ j, w j = v₀ ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (sM j) : GL (Fin 2) ℝ) := fun j =>
    SlashAction.slash_mul _ _ _ _

  have nicev₀ : Nice (Gamma (M * p)) k v₀ :=
    nice_slash_of_conj δ (det_heckeMatrix_pos p 0) (fun h => dInvEquiv hpMp hp0 h)
      (dInvEquiv_spec hpMp hp0) hΛ₀le F
  have nicew : ∀ j, Nice (Gamma (M * p)) k (w j) := by
    intro j
    refine nice_slash_of_conj (δ * (Matrix.SpecialLinearGroup.mapGL ℝ (sM j) : GL (Fin 2) ℝ)) ?_
      (fun h => dInvEquiv hpMp hp0 (conjEquiv (M * p) (sM j) h)) (fun h => ?_) hΛ₀le F
    · rw [map_mul, Units.val_mul, det_heckeMatrix hp0 0, det_mapGL, mul_one]; exact hpR
    · rw [mul_assoc, conjEquiv_spec (M * p) (sM j) h, ← mul_assoc, dInvEquiv_spec hpMp hp0, mul_assoc]

  have hwp : w p = ε (p : ZMod M) • ((⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix p) := by
    show (⇑F : ℍ → ℂ) ∣[k] (δ * (Matrix.SpecialLinearGroup.mapGL ℝ (sM p) : GL (Fin 2) ℝ)) = _
    simp only [sM, lt_irrefl, if_false, hδ]
    rw [← gam0_mul_heckeDiag hp0 u v huv', SlashAction.slash_mul,
      slash_eq_smul_of_hasNebentypus hFneb (gam0_mem u v huv'), gam0_apply_11, Int.cast_natCast,
      ModularForm.smul_slash, σ_heckeDiagMatrix]
    rfl
  have hw0 : w 0 = v₀ := by
    show (⇑F : ℍ → ℂ) ∣[k] (δ * (Matrix.SpecialLinearGroup.mapGL ℝ (sM 0) : GL (Fin 2) ℝ)) = _
    simp only [sM, if_pos hp.pos, pow_zero, map_one, mul_one, hv₀]
  have hsum : ∑ j ∈ Finset.range (p + 1), w j = a • (⇑F : ℍ → ℂ) := by
    rw [Finset.sum_range_succ]
    have h1 : ∑ j ∈ Finset.range p, w j = heckeU k p ⇑F := by
      rw [heckeU_def]
      refine Finset.sum_congr rfl fun j hj => ?_
      show (⇑F : ℍ → ℂ) ∣[k] (δ * (Matrix.SpecialLinearGroup.mapGL ℝ (sM j) : GL (Fin 2) ℝ)) = _
      simp only [sM, if_pos (Finset.mem_range.mp hj), hδ]
      rw [← heckeMatrix_eq_delta_mul hp0 j]
    rw [h1, hwp]
    exact heckeT_eq_smul hp0 F (ε (p : ZMod M)) a ha

  set P : ℂ := pair (Gamma (M * p)) k ⇑F ⇑F with hP
  have hidx : (Lam0 (M * p) p).relIndex (Gamma1 M) = (Gamma (M * p)).relIndex (Gamma1 M) := by
    have hcard := card_quotient_eq_of_conj (Gamma (M * p)) (Lam0 (M * p) p) δ (dInvEquiv hpMp hp0)
      (dInvEquiv_spec hpMp hp0)
    have h1 := Subgroup.relIndex_mul_index hΛ₀le
    have h2 := Subgroup.relIndex_mul_index hΓle
    have e1 : (Lam0 (M * p) p).index = Fintype.card (SL(2, ℤ) ⧸ Lam0 (M * p) p) := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    have e2 : (Gamma (M * p)).index = Fintype.card (SL(2, ℤ) ⧸ Gamma (M * p)) := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    rw [e1, ← hcard, ← e2, ← h2] at h1
    have hI : (Gamma1 M).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hI) h1
  have hPΛ : pair (Lam0 (M * p) p) k ⇑F ⇑F = P := by
    rw [hP, pair_eq_relIndex_mul hΛ₀le niceF niceF, pair_eq_relIndex_mul hΓle niceF niceF, hidx]
  have hQ : ∀ j, pair (Gamma (M * p)) k (w j) (w j) = (p : ℂ) ^ (k - 2) * P := by
    intro j
    rw [hwj j, pair_slash (Gamma (M * p)) _ (by rw [det_mapGL]; exact one_pos) (conjEquiv (M * p) (sM j))
      (conjEquiv_spec (M * p) (sM j)) nicev₀ nicev₀, det_mapGL, Complex.ofReal_one, one_zpow, one_mul,
      hv₀, pair_slash (Lam0 (M * p) p) δ (det_heckeMatrix_pos p 0) (dInvEquiv hpMp hp0)
        (dInvEquiv_spec hpMp hp0) niceFΛ niceFΛ, det_heckeMatrix hp0 0, hPΛ, Complex.ofReal_natCast]

  obtain ⟨hPre, hPnn⟩ := pair_self_ofReal (Gamma (M * p)) (k := k) niceFΓ.cont
  rw [← hP] at hPre hPnn
  set Pr : ℝ := P.re with hPr
  have hP0 : P ≠ 0 := by
    intro h0
    apply hF0
    have h := eq_zero_of_pair_self_eq_zero (Gamma (M * p)) niceFΓ h0
    exact DFunLike.ext F 0 fun x => by simpa using congrFun h x
  have hPrpos : 0 < Pr := by
    refine lt_of_le_of_ne hPnn (fun h0 => hP0 ?_)
    rw [hPre, ← h0]; simp
  set Qr : ℝ := (p : ℝ) ^ (k - 2) * Pr with hQr
  have hQr : ∀ j, pair (Gamma (M * p)) k (w j) (w j) = (Qr : ℂ) := by
    intro j; rw [hQ j, hPre, hQr]; push_cast; ring
  have hQrpos : 0 < Qr := mul_pos (zpow_pos hpR _) hPrpos

  have hterm : ∀ i j, (pair (Gamma (M * p)) k (w i) (w j)).re ≤ Qr := by
    intro i j
    have hcs := norm_pair_sq_le (Gamma (M * p)) (nicew i) (nicew j)
    rw [hQr i, hQr j, Complex.ofReal_re] at hcs
    have hle : ‖pair (Gamma (M * p)) k (w i) (w j)‖ ≤ Qr := by
      nlinarith [norm_nonneg (pair (Gamma (M * p)) k (w i) (w j)), hQrpos]
    exact (Complex.re_le_norm _).trans hle

  set s : Finset ℕ := Finset.range (p + 1) with hs
  have hexp : pair (Gamma (M * p)) k (a • ⇑F) (a • ⇑F)
      = ∑ i ∈ s, ∑ j ∈ s, pair (Gamma (M * p)) k (w i) (w j) := by
    rw [← hsum, pair_sum_left (Gamma (M * p)) s w _ nicew (Nice.sum s fun j => nicew j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pair_sum_right (Gamma (M * p)) s (w i) w (nicew i) nicew]
  have hlhs : pair (Gamma (M * p)) k (a • ⇑F) (a • ⇑F) = ((‖a‖ ^ 2 * Pr : ℝ) : ℂ) := by
    rw [pair_smul_left, pair_smul_right, ← hP, ← mul_assoc, Complex.conj_mul', hPre]
    push_cast; ring
  have hre : ‖a‖ ^ 2 * Pr = ∑ i ∈ s, ∑ j ∈ s, (pair (Gamma (M * p)) k (w i) (w j)).re := by
    have h := congrArg Complex.re (hlhs.symm.trans hexp)
    rw [Complex.ofReal_re, Complex.re_sum] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
  have h0s : 0 ∈ s := Finset.mem_range.mpr (Nat.succ_pos p)
  have hps : p ∈ s := Finset.mem_range.mpr (Nat.lt_succ_self p)
  have hcard : s.card = p + 1 := Finset.card_range (p + 1)

  have hB : ((p : ℝ) + 1) ^ 2 * (p : ℝ) ^ (k - 2) * Pr = ∑ i ∈ s, ∑ j ∈ s, Qr := by
    simp only [Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast; ring
  by_cases hlt : (pair (Gamma (M * p)) k (w 0) (w p)).re < Qr
  ·
    have hstrict : ∑ i ∈ s, ∑ j ∈ s, (pair (Gamma (M * p)) k (w i) (w j)).re < ∑ i ∈ s, ∑ j ∈ s, Qr := by
      refine Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum fun j _ => hterm i j) ⟨0, h0s, ?_⟩
      exact Finset.sum_lt_sum (fun j _ => hterm 0 j) ⟨p, hps, hlt⟩
    rw [← hre, ← hB] at hstrict
    exact lt_of_mul_lt_mul_right hstrict hPrpos.le
  ·
    exfalso
    have heq : (pair (Gamma (M * p)) k (w 0) (w p)).re = Qr := le_antisymm (hterm 0 p) (not_lt.mp hlt)
    have hdiff : Nice (Gamma (M * p)) k (w 0 - w p) := (nicew 0).sub (nicew p)
    have hzero : pair (Gamma (M * p)) k (w 0 - w p) (w 0 - w p) = 0 := by
      set z : ℂ := pair (Gamma (M * p)) k (w 0) (w p) with hz
      have hzc : pair (Gamma (M * p)) k (w p) (w 0) = conj z := pair_conj_symm _ (w 0) (w p)
      rw [pair_sub_left' _ (nicew 0) (nicew p) hdiff, pair_sub_right' _ (nicew 0) (nicew p) (nicew 0),
        pair_sub_right' _ (nicew 0) (nicew p) (nicew p), hQr 0, hQr p, hzc, ← hz]
      have hzz : z + conj z = 2 * (Qr : ℂ) := by rw [Complex.add_conj, heq]; push_cast; ring
      linear_combination -hzz
    have hw0p : w 0 = w p := sub_eq_zero.mp (eq_zero_of_pair_self_eq_zero (Gamma (M * p)) hdiff hzero)
    rw [hw0, hwp, hv₀] at hw0p
    exact hF0 (eq_zero_of_slash_delta_eq hp F hεnorm hw0p)

end main

end HeckeBoundGamma1
p2m_reactivate "P2MW.S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.HeckeBoundGamma1"

end
p2m_reactivate "P2MW.S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.HeckeBoundGamma1"

open scoped MatrixGroups in

theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff g (p * n)
      + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0)
        = a * ModularFormClass.qCoeff g n) :
    ‖a‖ ^ 2 < ((p : ℝ) + 1) ^ 2 * (p : ℝ) ^ (k - 2) :=
  HeckeBoundGamma1.norm_sq_lt ε g hg0 hg hp hpM a ha

end S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen
end P2MW
export P2MW.S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen (solution)
