-- Prove2me | solution 1 for FixedPointAA.Main.rotation_identities
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:13:51.211283+00:00
-- url     : https://prove2.me/submissions/2922c1b5-4765-44e5-834f-1a3147128ce2

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting
set_option autoImplicit false
open FixedPointAA.Main
open scoped Matrix

lemma fg_exp_smul_sq_one (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M * M = 1) (z : ℂ) :
    NormedSpace.exp (z • M) = Complex.cosh z • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Complex.sinh z • M := by
  have hM2 : M ^ 2 = 1 := by rw [sq]; exact hM
  have hev : ∀ n : ℕ, (z • M) ^ (2 * n) = z ^ (2 * n) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro n; rw [smul_pow, pow_mul M 2 n, hM2, one_pow]
  have hod : ∀ n : ℕ, (z • M) ^ (2 * n + 1) = z ^ (2 * n + 1) • M := by
    intro n; rw [smul_pow, pow_succ M, pow_mul M 2 n, hM2, one_pow, one_mul]
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • M)
  have he := (Complex.hasSum_cosh z).smul_const (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have ho := (Complex.hasSum_sinh z).smul_const M
  have hs := HasSum.even_add_odd (f := fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • (z • M) ^ n) (by
    convert he using 1
    funext k; rw [hev, smul_smul]; congr 1; rw [div_eq_mul_inv, mul_comm]) (by
    convert ho using 1
    funext k; rw [hod, smul_smul]; congr 1; rw [div_eq_mul_inv, mul_comm])
  exact h.unique hs

lemma fg_R_eq (ϕ θ : ℝ) : R ϕ θ =
    !![(Real.cos (θ / 2) : ℂ) - Complex.I * (Real.sin (θ / 2) : ℂ) * (Real.cos ϕ : ℂ),
       -Complex.I * (Real.sin (θ / 2) : ℂ) * (Real.sin ϕ : ℂ);
       -Complex.I * (Real.sin (θ / 2) : ℂ) * (Real.sin ϕ : ℂ),
       (Real.cos (θ / 2) : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) * (Real.cos ϕ : ℂ)] := by
  have hP : ((Real.cos ϕ : ℂ) • pauliZ + (Real.sin ϕ : ℂ) • pauliX) *
      ((Real.cos ϕ : ℂ) • pauliZ + (Real.sin ϕ : ℂ) • pauliX) = 1 := by
    have h := Real.cos_sq_add_sin_sq ϕ
    have h' : (Real.cos ϕ : ℂ) ^ 2 + (Real.sin ϕ : ℂ) ^ 2 = 1 := by exact_mod_cast h
    generalize (Real.cos ϕ : ℂ) = c at h' ⊢
    generalize (Real.sin ϕ : ℂ) = s at h' ⊢
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliZ, pauliX, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination h'
  unfold R
  rw [fg_exp_smul_sq_one _ hP]
  have e1 : -(Complex.I * ((θ / 2 : ℝ) : ℂ)) = -(((θ / 2 : ℝ) : ℂ) * Complex.I) := by ring
  rw [e1, Complex.cosh_neg, Complex.sinh_neg, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, pauliX, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

lemma fg_A_eq (φ ζ : ℝ) : A φ ζ =
    !![(Real.cos (φ / 2) : ℂ),
       -Complex.I * (Real.sin (φ / 2) : ℂ) * Complex.exp (-((ζ : ℂ) * Complex.I));
       -Complex.I * (Real.sin (φ / 2) : ℂ) * Complex.exp ((ζ : ℂ) * Complex.I),
       (Real.cos (φ / 2) : ℂ)] := by
  have hP : ((Real.cos ζ : ℂ) • pauliX + (Real.sin ζ : ℂ) • pauliY) *
      ((Real.cos ζ : ℂ) • pauliX + (Real.sin ζ : ℂ) • pauliY) = 1 := by
    have h := Real.cos_sq_add_sin_sq ζ
    have h' : (Real.cos ζ : ℂ) ^ 2 + (Real.sin ζ : ℂ) ^ 2 = 1 := by exact_mod_cast h
    generalize (Real.cos ζ : ℂ) = c at h' ⊢
    generalize (Real.sin ζ : ℂ) = s at h' ⊢
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliY, pauliX, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
      simp [Complex.I_sq] <;> linear_combination h'
  unfold A
  rw [fg_exp_smul_sq_one _ hP]
  have e1 : -(Complex.I * ((φ / 2 : ℝ) : ℂ)) = -(((φ / 2 : ℝ) : ℂ) * Complex.I) := by ring
  rw [e1, Complex.cosh_neg, Complex.sinh_neg, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have ex1 : Complex.exp ((ζ : ℂ) * Complex.I) = (Real.cos ζ : ℂ) + (Real.sin ζ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have ex2 : Complex.exp (-((ζ : ℂ) * Complex.I)) = (Real.cos ζ : ℂ) - (Real.sin ζ : ℂ) * Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]; ring
  rw [ex1, ex2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, pauliX, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

lemma fg_Ss_eq (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (α : ℝ) :
    Ss (sVec lam) α =
      !![1 - (1 - Complex.exp (-(α : ℂ) * Complex.I)) * (1 - (lam : ℂ)),
          -(1 - Complex.exp (-(α : ℂ) * Complex.I)) * ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ);
          -(1 - Complex.exp (-(α : ℂ) * Complex.I)) * ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ),
          1 - (1 - Complex.exp (-(α : ℂ) * Complex.I)) * (lam : ℂ)] := by
  have hsq1 : ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt (1 - lam) : ℝ) : ℂ) = 1 - (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hsq2 : ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) = (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  have hsq3 : ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) = ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.sqrt_mul h0, mul_comm]
  have hsq4 : ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt (1 - lam) : ℝ) : ℂ) = ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ) := by
    rw [mul_comm]; exact hsq3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ss, sVec, Matrix.vecMulVec, hsq1, hsq2, hsq3, hsq4] <;> ring

lemma fg_bloch_cos (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Real.cos (blochAngle lam) = 1 - 2 * lam := by
  unfold blochAngle
  have hq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt h0
  rw [Real.cos_two_mul, Real.cos_arcsin, hq, Real.sq_sqrt (by linarith)]
  ring

lemma fg_bloch_sin (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Real.sin (blochAngle lam) = 2 * Real.sqrt (lam * (1 - lam)) := by
  unfold blochAngle
  have hs1 : Real.sqrt lam ≤ 1 := Real.sqrt_le_one.mpr h1
  have hs0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  rw [Real.sin_two_mul, Real.sin_arcsin (by linarith) hs1, Real.cos_arcsin, Real.sqrt_mul h0,
    Real.sq_sqrt h0]
  ring

lemma fg_exp_neg_half (x : ℝ) :
    Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) =
      (Real.cos (x / 2) : ℂ) - Complex.I * (Real.sin (x / 2) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

lemma fg_exp_pos_half (x : ℝ) :
    Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) =
      (Real.cos (x / 2) : ℂ) + Complex.I * (Real.sin (x / 2) : ℂ) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

lemma fg_exp_neg_full (x : ℝ) :
    Complex.exp (-(x : ℂ) * Complex.I) = Complex.exp (-((x / 2 : ℝ) : ℂ) * Complex.I) ^ 2 := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma fg_exp_pos_full (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) = Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) ^ 2 := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma fg_cs (x : ℝ) : (Real.cos x : ℂ) ^ 2 + (Real.sin x : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq x

lemma fg_St_eq (β : ℝ) :
    St tVec β = !![1, 0; 0, Complex.exp ((β : ℂ) * Complex.I)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [St, tVec, Matrix.vecMulVec]

lemma fg_ep (ζ : ℝ) : Complex.exp ((ζ : ℂ) * Complex.I) = (Real.cos ζ : ℂ) + (Real.sin ζ : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma fg_em (ζ : ℝ) : Complex.exp (-((ζ : ℂ) * Complex.I)) = (Real.cos ζ : ℂ) - (Real.sin ζ : ℂ) * Complex.I := by
  rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]; ring

lemma fg_A_quarter (φ : ℝ) : A φ (Real.pi / 2) =
    !![(Real.cos (φ / 2) : ℂ), -(Real.sin (φ / 2) : ℂ); (Real.sin (φ / 2) : ℂ), (Real.cos (φ / 2) : ℂ)] := by
  rw [fg_A_eq, fg_ep, fg_em]
  have h1 : (Real.cos (Real.pi / 2) : ℂ) = 0 := by simp
  have h2 : (Real.sin (Real.pi / 2) : ℂ) = 1 := by simp
  rw [h1, h2]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  generalize (Real.sin (φ / 2) : ℂ) = S
  generalize (Real.cos (φ / 2) : ℂ) = C
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> first | linear_combination S * hI | linear_combination (-S) * hI

lemma fg_A_mquarter (φ : ℝ) : A φ (-Real.pi / 2) =
    !![(Real.cos (φ / 2) : ℂ), (Real.sin (φ / 2) : ℂ); -(Real.sin (φ / 2) : ℂ), (Real.cos (φ / 2) : ℂ)] := by
  rw [fg_A_eq, fg_ep, fg_em]
  have e : -Real.pi / 2 = -(Real.pi / 2) := by ring
  rw [e]
  have h1 : (Real.cos (-(Real.pi / 2)) : ℂ) = 0 := by simp
  have h2 : (Real.sin (-(Real.pi / 2)) : ℂ) = -1 := by simp
  rw [h1, h2]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  generalize (Real.sin (φ / 2) : ℂ) = S
  generalize (Real.cos (φ / 2) : ℂ) = C
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> first | linear_combination S * hI | linear_combination (-S) * hI

lemma fg_R_conj (φ α : ℝ) : R φ α = A φ (Real.pi / 2) * R 0 α * A φ (-Real.pi / 2) := by
  have hc : Real.cos φ = Real.cos (φ / 2) ^ 2 - Real.sin (φ / 2) ^ 2 := by
    have : φ = 2 * (φ / 2) := by ring
    conv_lhs => rw [this]
    rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]
  have hs : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    have : φ = 2 * (φ / 2) := by ring
    conv_lhs => rw [this]
    rw [Real.sin_two_mul]
  have hcs := fg_cs (φ / 2)
  have hcs' := fg_cs (α / 2)
  have hcC : ((Real.cos φ : ℝ) : ℂ) = (Real.cos (φ / 2) : ℂ) ^ 2 - (Real.sin (φ / 2) : ℂ) ^ 2 := by
    rw [hc]; simp only [Complex.ofReal_sub, Complex.ofReal_pow]
  have hsC : ((Real.sin φ : ℝ) : ℂ) = 2 * (Real.sin (φ / 2) : ℂ) * (Real.cos (φ / 2) : ℂ) := by
    rw [hs]; simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [fg_R_eq, fg_R_eq, fg_A_quarter, fg_A_mquarter, hcC, hsC]
  simp only [Real.cos_zero, Real.sin_zero, Complex.ofReal_one, Complex.ofReal_zero]
  simp only [Matrix.mul_fin_two]
  generalize (Real.cos (φ / 2) : ℂ) = C at hcs ⊢
  generalize (Real.sin (φ / 2) : ℂ) = S at hcs ⊢
  generalize (Real.cos (α / 2) : ℂ) = c at hcs' ⊢
  generalize (Real.sin (α / 2) : ℂ) = s at hcs' ⊢
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-c) * hcs
  · ring
  · ring
  · linear_combination (-c) * hcs

lemma fg_A_shift (φ α β : ℝ) : A φ (α + β) = R 0 β * A φ α * R 0 (-β) := by
  have hcs' := fg_cs (β / 2)
  have hexp1 : Complex.exp (-(((α + β : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-((α : ℂ) * Complex.I)) * ((Real.cos (β / 2) : ℂ) - Complex.I * (Real.sin (β / 2) : ℂ)) ^ 2 := by
    rw [← fg_exp_neg_half, ← neg_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← neg_mul]
    congr 1; push_cast; ring
  have hexp2 : Complex.exp ((((α + β : ℝ)) : ℂ) * Complex.I) =
      Complex.exp ((α : ℂ) * Complex.I) * ((Real.cos (β / 2) : ℂ) + Complex.I * (Real.sin (β / 2) : ℂ)) ^ 2 := by
    rw [← fg_exp_pos_half, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hneg : -β / 2 = -(β / 2) := by ring
  rw [fg_A_eq, fg_A_eq, fg_R_eq, fg_R_eq, hexp1, hexp2, hneg]
  simp only [Real.cos_zero, Real.sin_zero, Real.cos_neg, Real.sin_neg, Complex.ofReal_one,
    Complex.ofReal_zero, Complex.ofReal_neg]
  simp only [Matrix.mul_fin_two]
  generalize (Real.cos (β / 2) : ℂ) = c at hcs' ⊢
  generalize (Real.sin (β / 2) : ℂ) = s at hcs' ⊢
  generalize (Real.cos (φ / 2) : ℂ) = C
  generalize (Real.sin (φ / 2) : ℂ) = S
  generalize Complex.exp (-((α : ℂ) * Complex.I)) = Ea
  generalize Complex.exp ((α : ℂ) * Complex.I) = Eb
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-C) * hcs' + (C * s ^ 2) * hI
  · ring
  · ring
  · linear_combination (-C) * hcs' + (C * s ^ 2) * hI

theorem solution (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (α β : ℝ) :
    A (blochAngle lam) (Real.pi / 2) *ᵥ tbarVec = sVec lam ∧
    R (blochAngle lam) α =
      A (blochAngle lam) (Real.pi / 2) * R 0 α * A (blochAngle lam) (-Real.pi / 2) ∧
    A (blochAngle lam) (α + β) =
      R 0 β * A (blochAngle lam) α * R 0 (-β) := by
  refine ⟨?_, fg_R_conj _ _, fg_A_shift _ _ _⟩
  have hs1 : Real.sqrt lam ≤ 1 := Real.sqrt_le_one.mpr h1
  have hs0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have hhalf : blochAngle lam / 2 = Real.arcsin (Real.sqrt lam) := by unfold blochAngle; ring
  have hC : Real.cos (blochAngle lam / 2) = Real.sqrt (1 - lam) := by
    rw [hhalf, Real.cos_arcsin, Real.sq_sqrt h0]
  have hS : Real.sin (blochAngle lam / 2) = Real.sqrt lam := by
    rw [hhalf, Real.sin_arcsin (by linarith) hs1]
  rw [fg_A_quarter, hC, hS]
  ext i
  fin_cases i <;> simp [sVec, tbarVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
