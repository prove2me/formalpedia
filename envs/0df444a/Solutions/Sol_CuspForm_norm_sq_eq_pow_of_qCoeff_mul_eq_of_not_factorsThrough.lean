-- Prove2me | solution 1 for CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ef8fb1a1-99d2-5f36-b4dc-54d3f59e4374

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

namespace P2MW.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter CongruenceSubgroup
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace LiNormSq

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

def tGL (ℓ : ℕ) (n : ℤ) : GL (Fin 2) ℝ := upperTriangularGL 1 ((n : ℝ) / ℓ) 1 (by norm_num)

@[scoped simp] theorem val_tGL (ℓ : ℕ) (n : ℤ) :
    ((tGL ℓ n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (n : ℝ) / ℓ; 0, 1] := rfl

theorem det_tGL (ℓ : ℕ) (n : ℤ) : ((tGL ℓ n).det : ℝ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_tGL, Matrix.det_fin_two_of]; ring

theorem det_tGL_pos (ℓ : ℕ) (n : ℤ) : 0 < ((tGL ℓ n).det : ℝ) := by rw [det_tGL]; exact one_pos

theorem tGL_add (ℓ : ℕ) (m n : ℤ) : tGL ℓ m * tGL ℓ n = tGL ℓ (m + n) := by
  apply Units.ext
  rw [Units.val_mul, val_tGL, val_tGL, val_tGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem tGL_zero (ℓ : ℕ) : tGL ℓ 0 = 1 := by
  apply Units.ext; rw [val_tGL]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem tGL_neg_mul (ℓ : ℕ) (n : ℤ) : tGL ℓ (-n) * tGL ℓ n = 1 := by
  rw [tGL_add, neg_add_cancel, tGL_zero]

theorem tGL_inv (ℓ : ℕ) (n : ℤ) : (tGL ℓ n)⁻¹ = tGL ℓ (-n) :=
  inv_eq_of_mul_eq_one_left (tGL_neg_mul ℓ n)

theorem tGL_self (hℓ : ℓ ≠ 0) : tGL ℓ (ℓ : ℤ) = (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [val_tGL, val_mapGL_eq]
  have hℓ' : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, hℓ']

theorem tGL_smul (ℓ : ℕ) (n : ℤ) (τ : ℍ) : tGL ℓ n • τ = ((n : ℝ) / ℓ) +ᵥ τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_tGL_pos ℓ n), coe_vadd]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_tGL]
  ring

theorem slash_tGL_apply (ℓ : ℕ) (n : ℤ) (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] tGL ℓ n) τ = F (tGL ℓ n • τ) := by
  rw [ModularForm.slash_apply]
  have hσ : UpperHalfPlane.σ (tGL ℓ n) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos (det_tGL_pos ℓ n)]
  rw [hσ, det_tGL]
  simp [UpperHalfPlane.denom, val_tGL]

def tConjMat (M ℓ : ℕ) (n : ℤ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0 + n * (γ 1 0 / ℓ), γ 0 1 + n * ((γ 1 1 - γ 0 0) / ℓ) - n ^ 2 * (γ 1 0 / (ℓ * ℓ));
    γ 1 0, γ 1 1 - n * (γ 1 0 / ℓ)]

theorem exact_divs (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Lam0 M ℓ) :
    (ℓ : ℤ) * (γ 1 0 / ℓ) = γ 1 0 ∧ (ℓ : ℤ) * ((γ 1 1 - γ 0 0) / ℓ) = γ 1 1 - γ 0 0 ∧
      ((ℓ : ℤ) * ℓ) * (γ 1 0 / (ℓ * ℓ)) = γ 1 0 := by
  obtain ⟨h1, h2, -, h4⟩ := hγ
  have hℓM' : (ℓ : ℤ) ∣ M := Int.natCast_dvd_natCast.mpr hℓM
  refine ⟨Int.mul_ediv_cancel' ?_, Int.mul_ediv_cancel' ?_, Int.mul_ediv_cancel' ?_⟩
  · exact (by push_cast; exact dvd_mul_left _ _ : (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ)).trans h4
  · have : γ 1 1 - γ 0 0 = (γ 1 1 - 1) - (γ 0 0 - 1) := by ring
    rw [this]; exact (hℓM'.trans h2).sub (hℓM'.trans h1)
  · have : (ℓ : ℤ) * ℓ ∣ ((M * ℓ : ℕ) : ℤ) := by push_cast; exact mul_dvd_mul_right hℓM' _
    exact this.trans h4

theorem det_tConjMat (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (n : ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ Lam0 M ℓ) :
    (tConjMat M ℓ n γ).det = 1 := by
  obtain ⟨e1, e2, e3⟩ := exact_divs hℓM hℓ hγ
  set C := γ 1 0 / (ℓ : ℤ)
  set E := (γ 1 1 - γ 0 0) / (ℓ : ℤ)
  set C₂ := γ 1 0 / ((ℓ : ℤ) * ℓ)
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have hC₂ : (ℓ : ℤ) * C₂ = C := by
    apply mul_left_cancel₀ hℓ'
    rw [← mul_assoc, e3, e1]
  rw [tConjMat, Matrix.det_fin_two_of]
  have hd := det_entries γ

  have key : (γ 1 0 : ℤ) * E = C * (γ 1 1 - γ 0 0) := by
    rw [← e2, ← e1]; ring
  have key2 : (γ 1 0 : ℤ) * C₂ = C * C := by
    rw [← e1]; linear_combination C * hC₂
  linear_combination hd + (-n) * key + n ^ 2 * key2

def tConj (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (n : ℤ) (γ : Lam0 M ℓ) : SL(2, ℤ) :=
  ⟨tConjMat M ℓ n γ, det_tConjMat hℓM hℓ n γ.2⟩

theorem tConj_mem (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (n : ℤ) (γ : Lam0 M ℓ) :
    tConj hℓM hℓ n γ ∈ Lam0 M ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := γ.2
  obtain ⟨e1, e2, e3⟩ := exact_divs hℓM hℓ γ.2
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have hMl : (M : ℤ) = (M / ℓ : ℕ) * ℓ := by exact_mod_cast (Nat.div_mul_cancel hℓM).symm

  have hC : (M : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 / ℓ := by
    obtain ⟨t, ht⟩ := h4
    have : (γ : SL(2, ℤ)) 1 0 / (ℓ : ℤ) = M * t := by
      apply mul_left_cancel₀ hℓ'
      rw [e1, ht]; push_cast; ring
    rw [this]; exact dvd_mul_right _ _
  have hE : ((M / ℓ : ℕ) : ℤ) ∣ ((γ : SL(2, ℤ)) 1 1 - (γ : SL(2, ℤ)) 0 0) / ℓ := by
    have hdiff : (M : ℤ) ∣ (γ : SL(2, ℤ)) 1 1 - (γ : SL(2, ℤ)) 0 0 := by
      have : (γ : SL(2, ℤ)) 1 1 - (γ : SL(2, ℤ)) 0 0 = ((γ : SL(2, ℤ)) 1 1 - 1) - ((γ : SL(2, ℤ)) 0 0 - 1) := by ring
      rw [this]; exact h2.sub h1
    obtain ⟨t, ht⟩ := hdiff
    have : ((γ : SL(2, ℤ)) 1 1 - (γ : SL(2, ℤ)) 0 0) / (ℓ : ℤ) = (M / ℓ : ℕ) * t := by
      apply mul_left_cancel₀ hℓ'
      rw [e2, ht, hMl]; ring
    rw [this]; exact dvd_mul_right _ _
  have hC₂ : ((M / ℓ : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 / (ℓ * ℓ) := by
    obtain ⟨t, ht⟩ := h4
    have : (γ : SL(2, ℤ)) 1 0 / ((ℓ : ℤ) * ℓ) = (M / ℓ : ℕ) * t := by
      apply mul_left_cancel₀ (mul_ne_zero hℓ' hℓ')
      rw [e3, ht, show ((M * ℓ : ℕ) : ℤ) = (M : ℤ) * ℓ by push_cast; ring, hMl]; ring
    rw [this]; exact dvd_mul_right _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (M : ℤ) ∣ tConjMat M ℓ n γ 0 0 - 1
    simp only [tConjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    have : (γ : SL(2, ℤ)) 0 0 + n * ((γ : SL(2, ℤ)) 1 0 / ℓ) - 1 = ((γ : SL(2, ℤ)) 0 0 - 1) + n * ((γ : SL(2, ℤ)) 1 0 / ℓ) := by ring
    rw [this]; exact h1.add (hC.mul_left _)
  · show (M : ℤ) ∣ tConjMat M ℓ n γ 1 1 - 1
    simp only [tConjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero]
    have : (γ : SL(2, ℤ)) 1 1 - n * ((γ : SL(2, ℤ)) 1 0 / ℓ) - 1 = ((γ : SL(2, ℤ)) 1 1 - 1) - n * ((γ : SL(2, ℤ)) 1 0 / ℓ) := by ring
    rw [this]; exact h2.sub (hC.mul_left _)
  · show ((M / ℓ : ℕ) : ℤ) ∣ tConjMat M ℓ n γ 0 1
    simp only [tConjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero]
    exact (h3.add (hE.mul_left _)).sub (hC₂.mul_left _)
  · show ((M * ℓ : ℕ) : ℤ) ∣ tConjMat M ℓ n γ 1 0
    simp only [tConjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one]
    exact h4

theorem tGL_mul_eq (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (n : ℤ) (γ : Lam0 M ℓ) :
    tGL ℓ n * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ (tConj hℓM hℓ n γ) : GL (Fin 2) ℝ) * tGL ℓ n := by
  obtain ⟨e1, e2, e3⟩ := exact_divs hℓM hℓ γ.2
  have hℓ' : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  set C := (γ : SL(2, ℤ)) 1 0 / (ℓ : ℤ) with hC
  set E := ((γ : SL(2, ℤ)) 1 1 - (γ : SL(2, ℤ)) 0 0) / (ℓ : ℤ) with hE
  set C₂ := (γ : SL(2, ℤ)) 1 0 / ((ℓ : ℤ) * ℓ) with hC₂
  have e1' : (ℓ : ℝ) * (C : ℝ) = ((γ : SL(2, ℤ)) 1 0 : ℝ) := by exact_mod_cast e1
  have e2' : (ℓ : ℝ) * (E : ℝ) = ((γ : SL(2, ℤ)) 1 1 : ℝ) - ((γ : SL(2, ℤ)) 0 0 : ℝ) := by exact_mod_cast e2
  have e3' : ((ℓ : ℝ) * ℓ) * (C₂ : ℝ) = ((γ : SL(2, ℤ)) 1 0 : ℝ) := by exact_mod_cast e3
  have hCr : (C : ℝ) = (ℓ : ℝ)⁻¹ * ((γ : SL(2, ℤ)) 1 0 : ℝ) := by
    rw [← e1', ← mul_assoc, inv_mul_cancel₀ hℓ', one_mul]
  have hEr : (E : ℝ) = (ℓ : ℝ)⁻¹ * (((γ : SL(2, ℤ)) 1 1 : ℝ) - ((γ : SL(2, ℤ)) 0 0 : ℝ)) := by
    rw [← e2', ← mul_assoc, inv_mul_cancel₀ hℓ', one_mul]
  have hC₂r : (C₂ : ℝ) = (ℓ : ℝ)⁻¹ * ((ℓ : ℝ)⁻¹ * ((γ : SL(2, ℤ)) 1 0 : ℝ)) := by
    rw [← e3']; field_simp
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_tGL, val_mapGL_eq, val_mapGL_eq]
  simp only [tConj, tConjMat, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  rw [← hC, ← hE, ← hC₂]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> simp only [div_eq_mul_inv, hCr, hEr, hC₂r] <;> ring

theorem mapGL_tConj (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (n : ℤ) (γ : Lam0 M ℓ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (tConj hℓM hℓ n γ) : GL (Fin 2) ℝ)
      = tGL ℓ n * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (tGL ℓ n)⁻¹ := by
  rw [tGL_mul_eq hℓM hℓ n γ, mul_inv_cancel_right]

def tEquiv (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (n : ℤ) : Lam0 M ℓ ≃ Lam0 M ℓ where
  toFun γ := ⟨tConj hℓM hℓ n γ, tConj_mem hℓM hℓ n γ⟩
  invFun γ := ⟨tConj hℓM hℓ (-n) γ, tConj_mem hℓM hℓ (-n) γ⟩
  left_inv γ := by
    apply Subtype.ext
    apply mapGL_injective
    show (Matrix.SpecialLinearGroup.mapGL ℝ (tConj hℓM hℓ (-n) ⟨tConj hℓM hℓ n γ, _⟩) : GL (Fin 2) ℝ) = _
    rw [mapGL_tConj, Subgroup.coe_mk, mapGL_tConj, tGL_inv, tGL_inv, neg_neg, ← mul_assoc, ← mul_assoc,
      tGL_neg_mul, one_mul, mul_assoc, tGL_add, neg_add_cancel, tGL_zero, mul_one]
  right_inv γ := by
    apply Subtype.ext
    apply mapGL_injective
    show (Matrix.SpecialLinearGroup.mapGL ℝ (tConj hℓM hℓ n ⟨tConj hℓM hℓ (-n) γ, _⟩) : GL (Fin 2) ℝ) = _
    rw [mapGL_tConj, Subgroup.coe_mk, mapGL_tConj, tGL_inv, tGL_inv, neg_neg, ← mul_assoc, ← mul_assoc,
      tGL_add, add_neg_cancel, tGL_zero, one_mul, mul_assoc, tGL_add, add_neg_cancel, tGL_zero, mul_one]

theorem tEquiv_spec (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (n : ℤ) (γ : Lam0 M ℓ) :
    tGL ℓ n * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((tEquiv hℓM hℓ n γ : Lam0 M ℓ) : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * tGL ℓ n :=
  tGL_mul_eq hℓM hℓ n γ

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
    simp only [Matrix.SpecialLinearGroup.coe_mk, dConjMat, Matrix.of_apply, Matrix.cons_val',
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
    simp only [mem_Lam0, Matrix.SpecialLinearGroup.coe_mk, dConjInvMat, Matrix.of_apply, Matrix.cons_val',
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

def dEquiv (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) : Lam0 M ℓ ≃ Gamma M where
  toFun := dConj hℓM
  invFun := dConjInv hℓM
  left_inv γ := by
    apply Subtype.ext
    apply mapGL_injective
    show (Matrix.SpecialLinearGroup.mapGL ℝ ((dConjInv hℓM (dConj hℓM γ) : Lam0 M ℓ) : SL(2, ℤ)) : GL (Fin 2) ℝ) = _
    rw [mapGL_dConjInv hℓM hℓ, mapGL_dConj hℓM hℓ]; group
  right_inv γ := by
    apply Subtype.ext
    apply mapGL_injective
    show (Matrix.SpecialLinearGroup.mapGL ℝ ((dConj hℓM (dConjInv hℓM γ) : Gamma M) : SL(2, ℤ)) : GL (Fin 2) ℝ) = _
    rw [mapGL_dConj hℓM hℓ, mapGL_dConjInv hℓM hℓ]; group

theorem dEquiv_spec (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (γ : Lam0 M ℓ) :
    heckeDiagMatrix ℓ * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((dEquiv hℓM hℓ γ : Gamma M) : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * heckeDiagMatrix ℓ :=
  heckeDiag_mul_eq hℓM hℓ γ

def lowSL (c : ℤ) : SL(2, ℤ) := ⟨!![1, 0; c, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem lowSL_apply (c : ℤ) (i j : Fin 2) : (lowSL c) i j = !![(1 : ℤ), 0; c, 1] i j := rfl

theorem lowSL_mem_Gamma1 {c : ℤ} (hc : (M : ℤ) ∣ c) : lowSL c ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp only [lowSL_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_one, true_and]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc

theorem lowSL_inv (c : ℤ) : (lowSL c)⁻¹ = lowSL (-c) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowSL]

theorem conj_lowSL_mem (hℓM : ℓ ∣ M) {c : ℤ} (hc : (M : ℤ) ∣ c) {γ : SL(2, ℤ)} (hγ : γ ∈ Lam0 M ℓ) :
    lowSL c * γ * (lowSL c)⁻¹ ∈ Lam0 M ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  rw [lowSL_inv]
  have e00 : (lowSL c * γ * lowSL (-c)) 0 0 = γ 0 0 - γ 0 1 * c := by
    simp [mul_apply', lowSL_apply]; ring
  have e01 : (lowSL c * γ * lowSL (-c)) 0 1 = γ 0 1 := by
    simp [mul_apply', lowSL_apply]
  have e10 : (lowSL c * γ * lowSL (-c)) 1 0 = c * (γ 0 0 - 1) - c * (γ 1 1 - 1) - c * c * γ 0 1 + γ 1 0 := by
    simp [mul_apply', lowSL_apply]; ring
  have e11 : (lowSL c * γ * lowSL (-c)) 1 1 = γ 1 1 + c * γ 0 1 := by
    simp [mul_apply', lowSL_apply]; ring
  have hMc : (M : ℤ) ∣ γ 0 1 * c := hc.mul_left _
  have hMℓ_MM : ((M * ℓ : ℕ) : ℤ) ∣ (M : ℤ) * M := by
    push_cast; exact mul_dvd_mul_left _ (Int.natCast_dvd_natCast.mpr hℓM)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, show γ 0 0 - γ 0 1 * c - 1 = (γ 0 0 - 1) - γ 0 1 * c by ring]; exact h1.sub hMc
  · rw [e11, show γ 1 1 + c * γ 0 1 - 1 = (γ 1 1 - 1) + c * γ 0 1 by ring]; exact h2.add (hc.mul_right _)
  · rw [e01]; exact h3
  · rw [e10]
    refine dvd_add (dvd_sub (dvd_sub ?_ ?_) ?_) h4
    · exact hMℓ_MM.trans (mul_dvd_mul hc h1)
    · exact hMℓ_MM.trans (mul_dvd_mul hc h2)
    · rw [mul_assoc]; exact hMℓ_MM.trans (mul_dvd_mul hc hMc |>.trans (by rw [mul_comm (γ 0 1)]))

def lowEquiv (hℓM : ℓ ∣ M) {c : ℤ} (hc : (M : ℤ) ∣ c) : Lam0 M ℓ ≃ Lam0 M ℓ where
  toFun γ := ⟨lowSL c * (γ : SL(2, ℤ)) * (lowSL c)⁻¹, conj_lowSL_mem hℓM hc γ.2⟩
  invFun γ := ⟨lowSL (-c) * (γ : SL(2, ℤ)) * (lowSL (-c))⁻¹, conj_lowSL_mem hℓM (dvd_neg.mpr hc) γ.2⟩
  left_inv γ := by
    apply Subtype.ext
    show lowSL (-c) * (lowSL c * (γ : SL(2, ℤ)) * (lowSL c)⁻¹) * (lowSL (-c))⁻¹ = γ
    rw [← lowSL_inv c, inv_inv]; group
  right_inv γ := by
    apply Subtype.ext
    show lowSL c * (lowSL (-c) * (γ : SL(2, ℤ)) * (lowSL (-c))⁻¹) * (lowSL c)⁻¹ = γ
    rw [← lowSL_inv c, inv_inv]; group

theorem lowEquiv_spec (hℓM : ℓ ∣ M) {c : ℤ} (hc : (M : ℤ) ∣ c) (γ : Lam0 M ℓ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (lowSL c) : GL (Fin 2) ℝ)
        * (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((lowEquiv hℓM hc γ : Lam0 M ℓ) : SL(2, ℤ)) : GL (Fin 2) ℝ)
          * (Matrix.SpecialLinearGroup.mapGL ℝ (lowSL c) : GL (Fin 2) ℝ) := by
  show _ = (Matrix.SpecialLinearGroup.mapGL ℝ (lowSL c * (γ : SL(2, ℤ)) * (lowSL c)⁻¹) : GL (Fin 2) ℝ) * _
  rw [map_mul, map_mul, map_inv, inv_mul_cancel_right]

end groups

section qexp

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ} {ℓ : ℕ}

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

theorem qParam_tGL_smul (hℓ : ℓ ≠ 0) (u : ℕ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((tGL ℓ (u : ℤ) • τ : ℍ) : ℂ)
      = Function.Periodic.qParam 1 (τ : ℂ) * Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ u := by
  rw [tGL_smul, coe_vadd, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  field_simp
  ring

theorem qParam_heckeDiag_smul (hℓ : ℓ ≠ 0) (τ : ℍ) :
    Function.Periodic.qParam 1 ((heckeDiagMatrix ℓ • τ : ℍ) : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ ℓ := by
  rw [coe_heckeDiagMatrix_smul hℓ, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem geom_sum_root (hℓ : ℓ ≠ 0) (n : ℕ) :
    ∑ u ∈ Finset.range ℓ, (Complex.exp (2 * Real.pi * Complex.I / ℓ) ^ u) ^ n
      = if ℓ ∣ n then (ℓ : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp ℓ hℓ
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ℓ)
  have hx : ∀ u : ℕ, (ζ ^ u) ^ n = (ζ ^ n) ^ u := fun u => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [hx]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd n).mpr h]
    simp
  · have hne : ζ ^ n ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd n).mp h1)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem sum_apply_tGL_smul (hℓ : ℓ ≠ 0) (F : CuspForm Γ₁(M) k) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff F (ℓ * n) = a * ModularFormClass.qCoeff F n) (τ : ℍ) :
    ∑ u ∈ Finset.range ℓ, F (tGL ℓ (u : ℤ) • τ) = (ℓ : ℂ) * a * F (heckeDiagMatrix ℓ • τ) := by
  set c : ℕ → ℂ := fun n => (qExpansion 1 F).coeff n with hc
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hq
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ℓ) with hζ
  have ha' : ∀ m : ℕ, c (ℓ * m) = a * c m := fun m => ha m

  set g : ℕ → ℂ := fun n => (if ℓ ∣ n then (ℓ : ℂ) else 0) * (c n * q ^ n) with hg

  have h1 : HasSum g (∑ u ∈ Finset.range ℓ, F (tGL ℓ (u : ℤ) • τ)) := by
    have hu : ∀ u ∈ Finset.range ℓ,
        HasSum (fun n : ℕ => c n * (q ^ n * (ζ ^ u) ^ n)) (F (tGL ℓ (u : ℤ) • τ)) := by
      intro u _
      have h := hasSum_F F (tGL ℓ (u : ℤ) • τ)
      simp only [qParam_tGL_smul hℓ u τ, smul_eq_mul, mul_pow] at h
      exact h
    have hs := hasSum_sum hu
    refine hs.congr_fun fun n => ?_
    show (if ℓ ∣ n then (ℓ : ℂ) else 0) * (c n * q ^ n) = ∑ i ∈ Finset.range ℓ, c n * (q ^ n * (ζ ^ i) ^ n)
    have : ∀ i : ℕ, c n * (q ^ n * (ζ ^ i) ^ n) = (c n * q ^ n) * (ζ ^ i) ^ n := fun i => by ring
    simp only [this]
    rw [← Finset.mul_sum, geom_sum_root hℓ n]
    ring

  have h2 : HasSum (fun m : ℕ => g (ℓ * m)) ((ℓ : ℂ) * a * F (heckeDiagMatrix ℓ • τ)) := by
    have h := (hasSum_F F (heckeDiagMatrix ℓ • τ)).mul_left ((ℓ : ℂ) * a)
    simp only [qParam_heckeDiag_smul hℓ τ, smul_eq_mul] at h
    refine h.congr_fun fun m => ?_
    simp only [hg, if_pos (dvd_mul_right ℓ m), ha' m, ← hq, pow_mul]
    ring

  have h3 : HasSum g ((ℓ : ℂ) * a * F (heckeDiagMatrix ℓ • τ)) := by
    refine (Function.Injective.hasSum_iff (mul_right_injective₀ hℓ) ?_).mp h2
    intro x hx
    have hnd : ¬ ℓ ∣ x := fun ⟨m, hm⟩ => hx ⟨m, hm.symm⟩
    simp only [hg, if_neg hnd, zero_mul]
  exact h1.unique h3

theorem sum_slash_tGL (hℓ : ℓ ≠ 0) (F : CuspForm Γ₁(M) k) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff F (ℓ * n) = a * ModularFormClass.qCoeff F n) :
    ∑ u ∈ Finset.range ℓ, ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ (u : ℤ))
      = (a * (ℓ : ℂ) ^ (2 - k)) • ((⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix ℓ) := by
  funext τ
  rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, slash_heckeDiagMatrix_apply k hℓ]
  simp only [slash_tGL_apply]
  rw [sum_apply_tGL_smul hℓ F a ha τ]
  have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  rw [show (2 : ℤ) - k = 1 - (k - 1) by ring, zpow_sub₀ hℓ', zpow_one]
  field_simp

end qexp

section main

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ} {k : ℤ} {ℓ : ℕ}

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

theorem nice_slash_tGL [NeZero M] (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (F : CuspForm Γ₁(M) k) (n : ℤ) :
    Nice (Lam0 M ℓ) k ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ n) := by
  have hF := nice_cuspForm F
  obtain ⟨C, hC⟩ := hF.bdd
  refine ⟨(F.holo'.slash k _).continuous, ⟨C, fun x => ?_⟩, fun h hh => ?_⟩
  · rw [dens_slash (det_tGL_pos ℓ n), det_tGL, one_zpow, one_mul]; exact hC _
  · rw [← SlashAction.slash_mul, tEquiv_spec hℓM hℓ n ⟨h, hh⟩, SlashAction.slash_mul,
      hF.inv _ (Lam0_le_Gamma1 (tEquiv hℓM hℓ n ⟨h, hh⟩).2)]

theorem tGL_ell_mul (hℓ : ℓ ≠ 0) (j : ℤ) :
    tGL ℓ ((ℓ : ℤ) * j) = (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ j) : GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [val_tGL, val_mapGL_eq]
  have hℓ' : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
  have hT : ∀ i i', (ModularGroup.T ^ j) i i' = (!![(1 : ℤ), j; 0, 1]) i i' := fun i i' => by
    rw [← ModularGroup.coe_T_zpow j]
  ext i i'
  fin_cases i <;> fin_cases i' <;> simp [hT]
  field_simp

theorem slash_tGL_eq_of_emod [NeZero M] (hℓ : ℓ ≠ 0) (F : CuspForm Γ₁(M) k) {m n : ℤ}
    (h : (ℓ : ℤ) ∣ m - n) : (⇑F : ℍ → ℂ) ∣[k] tGL ℓ m = (⇑F : ℍ → ℂ) ∣[k] tGL ℓ n := by
  obtain ⟨j, hj⟩ := h
  have hm : m = (ℓ : ℤ) * j + n := by linarith
  rw [hm, ← tGL_add, tGL_ell_mul hℓ, SlashAction.slash_mul,
    (nice_cuspForm F).inv _ (zpow_mem (by
      rw [Gamma1_mem]; simp [ModularGroup.T]) j)]

variable [NeZero M] [Fact ℓ.Prime] [Fact (ℓ ∣ M)]

theorem pair_slash_tGL_tGL (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (F : CuspForm Γ₁(M) k) (u u' : ℤ) :
    pair (Lam0 M ℓ) k ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ u) ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ u')
      = pair (Lam0 M ℓ) k ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ (u - u')) ⇑F := by
  have h1 : (⇑F : ℍ → ℂ) ∣[k] tGL ℓ u = ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ (u - u')) ∣[k] tGL ℓ u' := by
    rw [← SlashAction.slash_mul, tGL_add, sub_add_cancel]
  have h2 : (⇑F : ℍ → ℂ) ∣[k] tGL ℓ u' = (⇑F : ℍ → ℂ) ∣[k] tGL ℓ u' := rfl
  rw [h1, pair_slash (Lam0 M ℓ) (tGL ℓ u') (det_tGL_pos ℓ u') (tEquiv hℓM hℓ u') (tEquiv_spec hℓM hℓ u')
    (nice_slash_tGL hℓM hℓ F (u - u')) ((nice_cuspForm F).mono Lam0_le_Gamma1), det_tGL, Complex.ofReal_one,
    one_zpow, one_mul]

def lowCocycleMat (c s b' d' : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![s, b'; c, d']

omit [NeZero M] [Fact (Nat.Prime ℓ)] [Fact (ℓ ∣ M)] in

theorem exists_lowCocycle (hℓM : ℓ ∣ M) (hℓ : ℓ ≠ 0) (u u' c₀ : ℤ)
    (h2 : (ℓ : ℤ) ∣ u - (1 + u * c₀ * (M / ℓ : ℕ)) * u') :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 M ∧ γ' 1 1 = 1 - c₀ * u' * (M / ℓ : ℕ) ∧
      tGL ℓ u * (Matrix.SpecialLinearGroup.mapGL ℝ (lowSL (M * c₀)) : GL (Fin 2) ℝ)
        = (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) * tGL ℓ u' := by
  set L : ℤ := ((M / ℓ : ℕ) : ℤ) with hL
  have hML : (M : ℤ) = L * ℓ := by rw [hL]; exact_mod_cast (Nat.div_mul_cancel hℓM).symm
  obtain ⟨b', hb'⟩ := h2

  have hdet : (lowCocycleMat (M * c₀) (1 + u * c₀ * L) b' (1 - c₀ * u' * L)).det = 1 := by
    rw [lowCocycleMat, Matrix.det_fin_two_of]
    have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
    apply mul_left_cancel₀ hℓ'
    linear_combination ((M : ℤ) * c₀) * hb' + (c₀ * (-u + u' + u * u' * c₀ * L)) * hML
  refine ⟨⟨lowCocycleMat (M * c₀) (1 + u * c₀ * L) b' (1 - c₀ * u' * L), hdet⟩, ?_, rfl, ?_⟩
  · rw [Gamma0_mem]
    show (((lowCocycleMat (M * c₀) (1 + u * c₀ * L) b' (1 - c₀ * u' * L)) 1 0 : ℤ) : ZMod M) = 0
    simp only [lowCocycleMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact dvd_mul_right _ _
  · have hℓ' : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
    have hb'R : (u : ℝ) - (1 + (u : ℝ) * c₀ * L) * u' = ℓ * b' := by exact_mod_cast hb'
    have hMLR : (M : ℝ) = (L : ℝ) * ℓ := by exact_mod_cast hML
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, val_tGL, val_tGL, val_mapGL_eq, val_mapGL_eq]
    simp only [Matrix.SpecialLinearGroup.coe_mk, lowCocycleMat, lowSL_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    rw [hMLR]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    all_goals (field_simp; try (first | ring1 | linear_combination hb'R))

omit [Fact ℓ.Prime] [Fact (ℓ ∣ M)] in
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

omit [Fact ℓ.Prime] [Fact (ℓ ∣ M)] in
theorem exists_unit_of_not_factorsThrough (hℓM : ℓ ∣ M) {ε : DirichletCharacter ℂ M}
    (hε : ¬ ε.FactorsThrough (M / ℓ)) :
    ∃ x : (ZMod M)ˣ, (((x : ZMod M).val : ℤ) : ZMod (M / ℓ)) = 1 ∧ ε (x : ZMod M) ≠ 1 := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.div_dvd_of_dvd hℓM)] at hε
  obtain ⟨x, hx1, hx2⟩ := Set.not_subset.mp hε
  refine ⟨x, ?_, ?_⟩
  · have h : ZMod.unitsMap (Nat.div_dvd_of_dvd hℓM) x = 1 := hx1
    rw [ZMod.unitsMap_def] at h
    have h' := congrArg (fun u : (ZMod (M / ℓ))ˣ => (u : ZMod (M / ℓ))) h
    simp only [Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply, Units.val_one] at h'
    rw [Int.cast_natCast, ← ZMod.cast_eq_val, h']
  · intro h1
    apply hx2
    change x ∈ (MulChar.toUnitHom ε).ker
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one]
    exact h1

theorem charStep_arith (hℓM : ℓ ∣ M) {d₀ m₀ : ℤ} (hd₀ : d₀ = 1 + (M / ℓ : ℕ) * m₀)
    (hd₀ℓ : (d₀ : ZMod ℓ) ≠ 0) {w : ZMod ℓ} (hw : w ≠ 0) :
    ∃ c₀ : ℤ, (ℓ : ℤ) ∣ c₀ * ((w * (d₀ : ZMod ℓ)).val : ℤ) + m₀ ∧
      (ℓ : ℤ) ∣ (w.val : ℤ) - (1 + (w.val : ℤ) * c₀ * (M / ℓ : ℕ)) * ((w * (d₀ : ZMod ℓ)).val : ℤ) := by
  set L : ℕ := M / ℓ with hLdef
  set u' : ZMod ℓ := w * (d₀ : ZMod ℓ) with hu'
  have hu'0 : u' ≠ 0 := mul_ne_zero hw hd₀ℓ
  refine ⟨((-(m₀ : ZMod ℓ) * u'⁻¹).val : ℤ), ?_, ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [mul_assoc, inv_mul_cancel₀ hu'0, mul_one, neg_add_cancel]
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hL : (L : ZMod ℓ) * (m₀ : ZMod ℓ) = (d₀ : ZMod ℓ) - 1 := by
      have := congrArg (Int.cast : ℤ → ZMod ℓ) hd₀
      simp only [Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast] at this
      rw [this]; ring
    have key : (1 + (w : ZMod ℓ) * (-(m₀ : ZMod ℓ) * u'⁻¹) * (L : ZMod ℓ)) * u' = w := by
      have e1 : (w : ZMod ℓ) * (-(m₀ : ZMod ℓ) * u'⁻¹) * (L : ZMod ℓ) * u'
          = -(w * ((L : ZMod ℓ) * (m₀ : ZMod ℓ))) := by
        field_simp
      rw [add_mul, one_mul, e1, hL, hu']
      ring
    rw [key, sub_self]

variable (hℓM : ℓ ∣ M) (ε : DirichletCharacter ℂ M) (F : CuspForm Γ₁(M) k) (hFneb : CuspForm.HasNebentypus ε F)

def phi (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ∣ M)] (F : CuspForm Γ₁(M) k) (n : ℤ) : ℂ :=
  pair (Lam0 M ℓ) k ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ n) ⇑F

theorem conj_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : conj (z⁻¹) = z := by
  have h1 : conj z * z = 1 := by
    rw [Complex.conj_mul', hz]; simp
  have h2 : conj z = z⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [map_inv₀, h2, inv_inv]

include hℓM hFneb in

theorem phi_mul {d₀ m₀ : ℤ} (hd₀ : d₀ = 1 + (M / ℓ : ℕ) * m₀) (hd₀ℓ : (d₀ : ZMod ℓ) ≠ 0)
    (hεd₀ : ‖ε (d₀ : ZMod M)‖ = 1) {w : ZMod ℓ} (hw : w ≠ 0) :
    phi ℓ F (((w * (d₀ : ZMod ℓ)).val : ℤ)) = ε (d₀ : ZMod M) * phi ℓ F (w.val : ℤ) := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  set L : ℕ := M / ℓ with hLdef
  obtain ⟨c₀, h1, h2⟩ := charStep_arith hℓM hd₀ hd₀ℓ hw
  obtain ⟨γ', hγ'0, hγ'11, hGL⟩ := exists_lowCocycle hℓM hℓ (w.val : ℤ) _ c₀ h2
  set u : ℤ := (w.val : ℤ) with hudef
  set u' : ℤ := ((w * (d₀ : ZMod ℓ)).val : ℤ) with hu'def
  have hMc : (M : ℤ) ∣ M * c₀ := dvd_mul_right _ _

  have hchar : ε ((γ' 1 1 : ℤ) : ZMod M) = ε (d₀ : ZMod M) := by
    congr 1
    rw [hγ'11, ZMod.intCast_eq_intCast_iff_dvd_sub, hd₀]
    obtain ⟨t, ht⟩ := h1
    have : (1 : ℤ) + (L : ℕ) * m₀ - (1 - c₀ * u' * (L : ℕ)) = (L : ℕ) * (c₀ * u' + m₀) := by ring
    rw [this, ht, ← mul_assoc]
    refine Dvd.dvd.mul_right ?_ _
    exact ⟨1, by rw [mul_one]; exact_mod_cast Nat.div_mul_cancel hℓM⟩

  set g : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ (lowSL (M * c₀)) : GL (Fin 2) ℝ) with hgdef
  have hX : ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ u) ∣[k] g = ε (d₀ : ZMod M) • ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ u') := by
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul, slash_eq_smul_of_hasNebentypus hFneb hγ'0, hchar,
      ModularForm.smul_slash]
    have hσ : UpperHalfPlane.σ (tGL ℓ u') = .refl ℝ ℂ := by rw [UpperHalfPlane.σ, if_pos (det_tGL_pos ℓ u')]
    rw [hσ]; rfl
  have hε0 : ε (d₀ : ZMod M) ≠ 0 := fun h => by rw [h, norm_zero] at hεd₀; exact zero_ne_one hεd₀
  have hFt : (⇑F : ℍ → ℂ) ∣[k] tGL ℓ u' = (ε (d₀ : ZMod M))⁻¹ • (((⇑F : ℍ → ℂ) ∣[k] tGL ℓ u) ∣[k] g) := by
    rw [hX, smul_smul, inv_mul_cancel₀ hε0, one_smul]
  have hFg : (⇑F : ℍ → ℂ) ∣[k] g = ⇑F :=
    (nice_cuspForm F).inv _ (lowSL_mem_Gamma1 hMc)
  have hdet : 0 < ((g.det : ℝ)) := by rw [hgdef]; simp
  have hdet1 : (((g.det : ℝ)) : ℂ) ^ (k - 2) = 1 := by
    have : ((g.det : ℝ)) = 1 := by rw [hgdef]; simp
    rw [this]; simp
  have hps := pair_slash (Lam0 M ℓ) g hdet (lowEquiv hℓM hMc) (lowEquiv_spec hℓM hMc)
    (nice_slash_tGL hℓM hℓ F u) ((nice_cuspForm F).mono Lam0_le_Gamma1)
  rw [hFg, hdet1, one_mul] at hps
  unfold phi
  rw [hFt, pair_smul_left, hps, conj_inv_of_norm_eq_one hεd₀]

omit [NeZero M] [Fact (ℓ ∣ M)] in

theorem sum_range_eq_sum_zmod {X : Type*} [AddCommMonoid X] (f : ℤ → X) :
    ∑ u ∈ Finset.range ℓ, f (u : ℕ) = ∑ w : ZMod ℓ, f (w.val : ℕ) := by
  refine Finset.sum_nbij' (fun u : ℕ => (u : ZMod ℓ)) (fun w : ZMod ℓ => w.val) (fun _ _ => Finset.mem_univ _)
    (fun w _ => Finset.mem_range.mpr (ZMod.val_lt w)) (fun u hu => ZMod.val_cast_of_lt (Finset.mem_range.mp hu))
    (fun w _ => ZMod.natCast_zmod_val w) (fun u hu => ?_)
  rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hu)]

include hℓM hFneb in

theorem norm_sq_eq (hε : ¬ ε.FactorsThrough (M / ℓ)) (hF0 : F ≠ 0) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff F (ℓ * n) = a * ModularFormClass.qCoeff F n) :
    ‖a‖ ^ 2 = (ℓ : ℝ) ^ (k - 1) := by
  have hℓp : ℓ.Prime := Fact.out
  have hℓ : ℓ ≠ 0 := hℓp.ne_zero
  set Λ₀ := Lam0 M ℓ with hΛ₀
  have niceF := nice_cuspForm F
  have niceF0 : Nice Λ₀ k ⇑F := niceF.mono Lam0_le_Gamma1
  have niceFG : Nice (Gamma M) k ⇑F := niceF.mono Gamma_le_Gamma1
  have niceFt : ∀ n : ℤ, Nice Λ₀ k ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ n) := nice_slash_tGL hℓM hℓ F

  set P : ℂ := pair Λ₀ k ⇑F ⇑F with hP
  have hP0 : P ≠ 0 := by
    intro h0
    apply hF0
    have h := eq_zero_of_pair_self_eq_zero Λ₀ niceF0 h0
    exact DFunLike.ext F 0 fun x => by simpa using congrFun h x

  obtain ⟨x, hx1, hx2⟩ := exists_unit_of_not_factorsThrough hℓM hε
  set d₀ : ℤ := ((x : ZMod M).val : ℤ) with hd₀def
  have hd₀M : ((d₀ : ℤ) : ZMod M) = x := by rw [hd₀def, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hεd₀ : ‖ε (d₀ : ZMod M)‖ = 1 := by rw [hd₀M]; exact ε.unit_norm_eq_one x
  have hε1 : ε (d₀ : ZMod M) ≠ 1 := by rw [hd₀M]; exact hx2
  obtain ⟨m₀, hm₀⟩ : ((M / ℓ : ℕ) : ℤ) ∣ d₀ - 1 := (intCast_eq_one_iff _ _).mp hx1
  have hd₀ : d₀ = 1 + (M / ℓ : ℕ) * m₀ := by linarith
  have hd₀ℓ : (d₀ : ZMod ℓ) ≠ 0 := by
    intro h
    rw [hd₀def, Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h
    have hcop := ZMod.val_coe_unit_coprime x
    have := Nat.eq_one_of_dvd_coprimes hcop h hℓM
    exact hℓp.one_lt.ne' this

  set Φ : ZMod ℓ → ℂ := fun w => phi ℓ F (w.val : ℤ) with hΦ
  have hΦmul : ∀ w : ZMod ℓ, w ≠ 0 → Φ (w * (d₀ : ZMod ℓ)) = ε (d₀ : ZMod M) * Φ w :=
    fun w hw => phi_mul hℓM ε F hFneb hd₀ hd₀ℓ hεd₀ hw
  have hS0 : ∑ w ∈ Finset.univ.erase (0 : ZMod ℓ), Φ w = 0 := by
    have hd : (d₀ : ZMod ℓ) ≠ 0 := hd₀ℓ
    have hbij : ∑ w ∈ Finset.univ.erase (0 : ZMod ℓ), Φ (w * (d₀ : ZMod ℓ))
        = ∑ w ∈ Finset.univ.erase (0 : ZMod ℓ), Φ w := by
      refine Finset.sum_nbij' (fun w => w * (d₀ : ZMod ℓ)) (fun w => w * (d₀ : ZMod ℓ)⁻¹) ?_ ?_ ?_ ?_ ?_
      · intro w hw
        exact Finset.mem_erase.mpr ⟨mul_ne_zero (Finset.mem_erase.mp hw).1 hd, Finset.mem_univ _⟩
      · intro w hw
        exact Finset.mem_erase.mpr ⟨mul_ne_zero (Finset.mem_erase.mp hw).1 (inv_ne_zero hd), Finset.mem_univ _⟩
      · intro w _; simp only [mul_assoc, mul_inv_cancel₀ hd, mul_one]
      · intro w _; simp only [mul_assoc, inv_mul_cancel₀ hd, mul_one]
      · intro w _; rfl
    have hsum : ∑ w ∈ Finset.univ.erase (0 : ZMod ℓ), Φ (w * (d₀ : ZMod ℓ))
        = ε (d₀ : ZMod M) * ∑ w ∈ Finset.univ.erase (0 : ZMod ℓ), Φ w := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w hw => hΦmul w (Finset.mem_erase.mp hw).1
    rw [hbij] at hsum
    have : (1 - ε (d₀ : ZMod M)) * ∑ w ∈ Finset.univ.erase (0 : ZMod ℓ), Φ w = 0 := by
      rw [sub_mul, one_mul, ← hsum, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hε1.symm)
  have hΦ0 : Φ 0 = P := by
    simp only [hΦ, phi, ZMod.val_zero, Nat.cast_zero, tGL_zero, SlashAction.slash_one]
    rfl
  have hSall : ∑ w : ZMod ℓ, Φ w = P := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod ℓ)), hS0, add_zero, hΦ0]

  set V : ℍ → ℂ := ∑ u ∈ Finset.range ℓ, ((⇑F : ℍ → ℂ) ∣[k] tGL ℓ (u : ℤ)) with hV
  have niceV : Nice Λ₀ k V := Nice.sum _ fun u => niceFt _

  have hV1 : pair Λ₀ k V V = (ℓ : ℂ) * P := by
    have step1 : pair Λ₀ k V V = ∑ u ∈ Finset.range ℓ, ∑ u' ∈ Finset.range ℓ, phi ℓ F ((u : ℤ) - (u' : ℤ)) := by
      rw [hV, pair_sum_left Λ₀ _ _ V (fun u => niceFt _) niceV]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [pair_sum_right Λ₀ _ _ _ (niceFt _) (fun u' => niceFt _)]
      refine Finset.sum_congr rfl fun u' _ => ?_
      exact pair_slash_tGL_tGL hℓM hℓ F _ _
    have step2 : ∑ u ∈ Finset.range ℓ, ∑ u' ∈ Finset.range ℓ, phi ℓ F ((u : ℤ) - (u' : ℤ))
        = ∑ w : ZMod ℓ, ∑ w' : ZMod ℓ, Φ (w - w') := by
      rw [sum_range_eq_sum_zmod (fun u => ∑ u' ∈ Finset.range ℓ, phi ℓ F (u - (u' : ℤ)))]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [sum_range_eq_sum_zmod (fun u' => phi ℓ F ((w.val : ℕ) - u'))]
      refine Finset.sum_congr rfl fun w' _ => ?_
      simp only [hΦ, phi]
      congr 1
      apply slash_tGL_eq_of_emod hℓ F
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, sub_self]
    have step3 : ∑ w : ZMod ℓ, ∑ w' : ZMod ℓ, Φ (w - w') = ∑ w' : ZMod ℓ, ∑ v : ZMod ℓ, Φ v := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w' _ => ?_
      exact Fintype.sum_equiv (Equiv.subRight w') _ _ fun _ => rfl
    rw [step1, step2, step3, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, hSall]

  set z : ℂ := a * (ℓ : ℂ) ^ (2 - k) with hz
  have hVD : V = z • ((⇑F : ℍ → ℂ) ∣[k] heckeDiagMatrix ℓ) := by
    rw [hV, hz]; exact sum_slash_tGL hℓ F a ha
  have hidx : (Lam0 M ℓ).relIndex (Gamma1 M) = (Gamma M).relIndex (Gamma1 M) := by
    have hcard := card_quotient_eq_of_conj (Lam0 M ℓ) (Gamma M) (heckeDiagMatrix ℓ) (dEquiv hℓM hℓ)
      (dEquiv_spec hℓM hℓ)
    have h1 := Subgroup.relIndex_mul_index (Lam0_le_Gamma1 (M := M) (ℓ := ℓ))
    have h2 := Subgroup.relIndex_mul_index (Gamma_le_Gamma1 (M := M))
    have e1 : (Lam0 M ℓ).index = Fintype.card (SL(2, ℤ) ⧸ Lam0 M ℓ) := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    have e2 : (Gamma M).index = Fintype.card (SL(2, ℤ) ⧸ Gamma M) := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    rw [e1, hcard, ← e2, ← h2] at h1
    have hI : (Gamma1 M).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hI) h1
  have hPG : pair (Gamma M) k ⇑F ⇑F = P := by
    rw [hP, pair_eq_relIndex_mul (Lam0_le_Gamma1 (M := M) (ℓ := ℓ)) niceF niceF,
      pair_eq_relIndex_mul (Gamma_le_Gamma1 (M := M)) niceF niceF, hidx]
  have hV2 : pair Λ₀ k V V = conj z * z * ((ℓ : ℂ) ^ (k - 2) * P) := by
    rw [hVD, pair_smul_left, pair_smul_right, ← mul_assoc,
      pair_slash (Gamma M) (heckeDiagMatrix ℓ) (det_heckeDiagMatrix_pos ℓ) (dEquiv hℓM hℓ) (dEquiv_spec hℓM hℓ)
        niceFG niceFG, det_heckeDiagMatrix hℓ, hPG]
    push_cast
    ring

  have hkey : (ℓ : ℂ) = conj z * z * (ℓ : ℂ) ^ (k - 2) := by
    have := hV1.symm.trans hV2
    rw [← mul_assoc] at this
    exact mul_right_cancel₀ hP0 this
  rw [Complex.conj_mul', hz, norm_mul, Complex.norm_zpow, Complex.norm_natCast] at hkey
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓp.pos
  have hreal : (ℓ : ℝ) = (‖a‖ * (ℓ : ℝ) ^ (2 - k)) ^ 2 * (ℓ : ℝ) ^ (k - 2) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_natCast, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_zpow,
      Complex.ofReal_natCast]
    exact hkey
  have h2 : (‖a‖ * (ℓ : ℝ) ^ (2 - k)) ^ 2 * (ℓ : ℝ) ^ (k - 2) = ‖a‖ ^ 2 * (ℓ : ℝ) ^ (2 - k) := by
    rw [mul_pow, ← zpow_natCast ((ℓ : ℝ) ^ (2 - k)) 2, ← zpow_mul, mul_assoc, ← zpow_add₀ hℓR.ne']
    congr 2
    push_cast; ring
  rw [h2] at hreal
  have h3 : ‖a‖ ^ 2 = (ℓ : ℝ) / (ℓ : ℝ) ^ (2 - k) := by
    rw [eq_div_iff (zpow_ne_zero _ hℓR.ne')]; exact hreal.symm
  rw [h3, div_eq_iff (zpow_ne_zero _ hℓR.ne'), ← zpow_add₀ hℓR.ne']
  rw [show k - 1 + (2 - k) = (1 : ℤ) by ring, zpow_one]

end main

end LiNormSq
p2m_reactivate "P2MW.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.LiNormSq"

end
p2m_reactivate "P2MW.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.LiNormSq"

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M)
    (hε : ¬ ε.FactorsThrough (M / ℓ)) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg0 : g ≠ 0)
    (hg : CuspForm.HasNebentypus ε g) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff g (ℓ * n) = a * ModularFormClass.qCoeff g n) :
    ‖a‖ ^ 2 = (ℓ : ℝ) ^ (k - 1) :=
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact (ℓ ∣ M) := ⟨hℓM⟩
  LiNormSq.norm_sq_eq hℓM ε g hg hε hg0 a ha

end S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
end P2MW
export P2MW.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough (solution)
