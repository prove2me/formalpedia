-- Prove2me | solution 1 for FixedPointAA.Main.amplitude_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:15:01.154355+00:00
-- url     : https://prove2.me/submissions/3daa1d99-979d-4a3b-968a-76258e4ee302

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

lemma fg_amp_step (φ : ℝ) (ζ : ℕ → ℝ) (k : ℕ) :
    (Aprod φ ζ (k + 1) *ᵥ tbarVec) 0 =
      (Real.cos (φ / 2) : ℂ) * (Aprod φ ζ k *ᵥ tbarVec) 0 +
        (-Complex.I * (Real.sin (φ / 2) : ℂ) * Complex.exp (-((ζ (k + 1) : ℂ) * Complex.I))) *
          (Aprod φ ζ k *ᵥ tbarVec) 1 ∧
    (Aprod φ ζ (k + 1) *ᵥ tbarVec) 1 =
      (-Complex.I * (Real.sin (φ / 2) : ℂ) * Complex.exp ((ζ (k + 1) : ℂ) * Complex.I)) *
          (Aprod φ ζ k *ᵥ tbarVec) 0 +
        (Real.cos (φ / 2) : ℂ) * (Aprod φ ζ k *ᵥ tbarVec) 1 := by
  have h : Aprod φ ζ (k + 1) = A φ (ζ (k + 1)) * Aprod φ ζ k := rfl
  rw [h, ← Matrix.mulVec_mulVec, fg_A_eq]
  constructor <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem solution (φ : ℝ) (ζ : ℕ → ℝ) :
    amp φ ζ 0 = 1 ∧ amp φ ζ 1 = (Real.cos (φ / 2) : ℂ) ∧
    ∀ h : ℕ, 2 ≤ h →
      amp φ ζ h =
        (Real.cos (φ / 2) : ℂ) *
          (1 + Complex.exp (-(((ζ h - ζ (h - 1) : ℝ) : ℂ) * Complex.I))) * amp φ ζ (h - 1) -
        Complex.exp (-(((ζ h - ζ (h - 1) : ℝ) : ℂ) * Complex.I)) * amp φ ζ (h - 2) := by
  have h0 : (Aprod φ ζ 0 *ᵥ tbarVec) 0 = 1 ∧ (Aprod φ ζ 0 *ᵥ tbarVec) 1 = 0 := by
    simp [Aprod, tbarVec]
  refine ⟨by simpa [amp] using h0.1, ?_, ?_⟩
  · have := (fg_amp_step φ ζ 0).1
    rw [h0.1, h0.2] at this
    simpa [amp] using this
  · intro h hh
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩
    have e1 : k + 2 - 1 = k + 1 := by omega
    have e2 : k + 2 - 2 = k := by omega
    rw [e1, e2]
    have H2 := (fg_amp_step φ ζ (k + 1)).1
    have H1a := (fg_amp_step φ ζ k).1
    have H1b := (fg_amp_step φ ζ k).2
    have hw : Complex.exp (-(((ζ (k + 2) - ζ (k + 1) : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (-((ζ (k + 1 + 1) : ℂ) * Complex.I)) * Complex.exp ((ζ (k + 1) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hx : Complex.exp ((ζ (k + 1) : ℂ) * Complex.I) * Complex.exp (-((ζ (k + 1) : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add]; simp
    unfold amp
    rw [hw, H2, H1b, H1a]
    have hcs := fg_cs (φ / 2)
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    generalize (Aprod φ ζ k *ᵥ tbarVec) 0 = a0
    generalize (Aprod φ ζ k *ᵥ tbarVec) 1 = b0
    generalize Complex.exp ((ζ (k + 1) : ℂ) * Complex.I) = x1 at hx ⊢
    generalize Complex.exp (-((ζ (k + 1) : ℂ) * Complex.I)) = y1 at hx ⊢
    generalize Complex.exp (-((ζ (k + 1 + 1) : ℂ) * Complex.I)) = y2
    generalize (Real.cos (φ / 2) : ℂ) = C at hcs ⊢
    generalize (Real.sin (φ / 2) : ℂ) = S at hcs ⊢
    linear_combination (C * Complex.I * S * b0 * y2) * hx + (-a0 * x1 * y2) * hcs + (S ^ 2 * a0 * x1 * y2) * hI
