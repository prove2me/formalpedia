-- Prove2me | solution 1 for FixedPointAA.Main.sequence_as_A_product
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:47:38.564177+00:00
-- url     : https://prove2.me/submissions/c0ce431b-f614-4cdf-a766-0b9711df4d29

import Definitions.Def_FixedPointAA_Main_Setting
import Theorems.Thm_FixedPointAA_Main_reflections_matrix_form
import Theorems.Thm_FixedPointAA_Main_reflections_as_rotations
import Theorems.Thm_FixedPointAA_Main_rotation_identities

open FixedPointAA.Main
open scoped Matrix

private lemma R0_eq (θ : ℝ) :
    R 0 θ = Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) •
      !![1, 0; 0, Complex.exp ((θ : ℂ) * Complex.I)] := by
  have hrot := (reflections_as_rotations 0 (le_refl 0) zero_le_one 0 θ).2
  have hmat := (reflections_matrix_form 0 (le_refl 0) zero_le_one 0 θ).2
  rw [hmat] at hrot
  calc R 0 θ
    _ = (Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)) • R 0 θ := by
        rw [← Complex.exp_add]
        have : -((θ / 2 : ℝ) : ℂ) * Complex.I + ((θ / 2 : ℝ) : ℂ) * Complex.I = 0 := by ring
        rw [this, Complex.exp_zero, one_smul]
    _ = Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) •
          (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) • R 0 θ) := by
        rw [mul_smul]
    _ = Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) •
          !![1, 0; 0, Complex.exp ((θ : ℂ) * Complex.I)] := by
        rw [← hrot]

private lemma R0_zero : R 0 0 = 1 := by
  rw [R0_eq 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma R0_add (a b : ℝ) : R 0 a * R 0 b = R 0 (a + b) := by
  rw [R0_eq a, R0_eq b, R0_eq (a + b), Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h1 : Complex.exp (-((a / 2 : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-((b / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(((a + b) / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : (!![1, 0; 0, Complex.exp ((a : ℂ) * Complex.I)] : Matrix (Fin 2) (Fin 2) ℂ) *
      !![1, 0; 0, Complex.exp ((b : ℂ) * Complex.I)] =
      !![1, 0; 0, Complex.exp (((a + b : ℝ) : ℂ) * Complex.I)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add, add_mul]
  rw [h1, h2]

private lemma R0_neg_mul_self (θ : ℝ) : R 0 (-θ) * R 0 θ = 1 := by
  rw [R0_add, neg_add_cancel, R0_zero]

private lemma R0_mul_neg_self (θ : ℝ) : R 0 θ * R 0 (-θ) = 1 := by
  rw [R0_add, add_neg_cancel, R0_zero]

private lemma exp_neg_two_pi_I : Complex.exp (-(2 * Real.pi : ℂ) * Complex.I) = 1 := by
  have h : -(2 * Real.pi : ℂ) * Complex.I = -((2 * Real.pi : ℂ) * Complex.I) := by ring
  rw [h, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

private lemma R0_sub_two_pi (θ : ℝ) : R 0 (θ - 2 * Real.pi) = (-1 : ℂ) • R 0 θ := by
  rw [sub_eq_add_neg, ← R0_add θ (-(2 * Real.pi))]
  have h2pi : R 0 (-(2 * Real.pi)) = (-1 : ℂ) • 1 := by
    rw [R0_eq (-(2 * Real.pi))]
    have he1 : Complex.exp (-((-(2 * Real.pi) / 2 : ℝ) : ℂ) * Complex.I) = -1 := by
      have : -((-(2 * Real.pi) / 2 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.exp_pi_mul_I]
    have he2 : Complex.exp (((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
      have : ((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I = -(2 * Real.pi : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, exp_neg_two_pi_I]
    rw [he1, he2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h2pi, Matrix.mul_smul, Matrix.mul_one]

private lemma R0_mul_A (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (ζ θ : ℝ) :
    R 0 θ * A (blochAngle lam) ζ = A (blochAngle lam) (ζ + θ) * R 0 θ := by
  have hconj := (rotation_identities lam h0 h1 ζ θ).2.2
  rw [hconj, Matrix.mul_assoc, R0_neg_mul_self, Matrix.mul_one]

private lemma A_mul_R0 (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (ζ θ : ℝ) :
    A (blochAngle lam) ζ * R 0 θ = R 0 θ * A (blochAngle lam) (ζ - θ) := by
  rw [R0_mul_A lam h0 h1 (ζ - θ) θ, sub_add_cancel]

private lemma A_add_two_pi (φ ζ : ℝ) : A φ (ζ + 2 * Real.pi) = A φ ζ := by
  dsimp [A]
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

private lemma Rφ_mul_R0 (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (α B : ℝ) :
    R (blochAngle lam) α * R 0 B =
      R 0 (α + B) * A (blochAngle lam) (Real.pi / 2 - α - B) *
        A (blochAngle lam) (-Real.pi / 2 - B) := by
  have hR := (rotation_identities lam h0 h1 α B).2.1
  calc R (blochAngle lam) α * R 0 B
    _ = A (blochAngle lam) (Real.pi / 2) * R 0 α *
          (A (blochAngle lam) (-Real.pi / 2) * R 0 B) := by
        rw [hR, Matrix.mul_assoc]
    _ = A (blochAngle lam) (Real.pi / 2) * R 0 α *
          (R 0 B * A (blochAngle lam) (-Real.pi / 2 - B)) := by
        rw [A_mul_R0 lam h0 h1 (-Real.pi / 2) B]
    _ = A (blochAngle lam) (Real.pi / 2) * (R 0 α * R 0 B) *
          A (blochAngle lam) (-Real.pi / 2 - B) := by
        simp only [Matrix.mul_assoc]
    _ = (A (blochAngle lam) (Real.pi / 2) * R 0 (α + B)) *
          A (blochAngle lam) (-Real.pi / 2 - B) := by
        rw [R0_add]
    _ = R 0 (α + B) * A (blochAngle lam) (Real.pi / 2 - α - B) *
          A (blochAngle lam) (-Real.pi / 2 - B) := by
        rw [A_mul_R0 lam h0 h1 (Real.pi / 2) (α + B)]
        have : Real.pi / 2 - (α + B) = Real.pi / 2 - α - B := by ring
        rw [this]

private lemma arccot_neg (y : ℝ) : arccot (-y) = Real.pi - arccot y := by
  dsimp [arccot]
  rw [Real.arctan_neg]
  ring

private lemma tan_pi_sub (x : ℝ) : Real.tan (Real.pi - x) = -Real.tan x := by
  have : Real.pi - x = -(x - Real.pi) := by ring
  rw [this, Real.tan_neg, Real.tan_sub_pi]

private lemma neg_one_pow_odd_sub (l k : ℕ) (hk : k ≤ 2 * l + 1) :
    (-1 : ℝ) ^ (2 * l + 1 - k) = -((-1 : ℝ) ^ k) := by
  have h1 : (-1 : ℝ) ^ (2 * l + 1 - k) * (-1 : ℝ) ^ k = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hk, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  have h2 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc (-1 : ℝ) ^ (2 * l + 1 - k)
    _ = (-1 : ℝ) ^ (2 * l + 1 - k) * ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) := by rw [h2, mul_one]
    _ = ((-1 : ℝ) ^ (2 * l + 1 - k) * (-1 : ℝ) ^ k) * (-1 : ℝ) ^ k := by ring
    _ = -((-1 : ℝ) ^ k) := by rw [h1, neg_one_mul]

private lemma dz_symm (l : ℕ) (δ : ℝ) (k : ℕ) (hk : k ≤ 2 * l + 1) :
    dz l δ (2 * l + 1 - k) = -dz l δ k - 2 * Real.pi := by
  dsimp [dz]
  rw [neg_one_pow_odd_sub l k hk]
  have hL : (2 * (l : ℝ) + 1) ≠ 0 := by positivity
  have harg : ((2 * l + 1 - k : ℕ) : ℝ) * Real.pi / (2 * (l : ℝ) + 1) =
      Real.pi - (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1) := by
    rw [Nat.cast_sub hk]
    push_cast
    field_simp
  rw [harg, tan_pi_sub, neg_mul, neg_mul, arccot_neg]
  ring

private lemma dz_even (l : ℕ) (δ : ℝ) (j : ℕ) :
    dz l δ (2 * j + 2) = Real.pi - alpha l δ (j + 1) := by
  dsimp [dz, alpha]
  have hpow : (-1 : ℝ) ^ (2 * j + 2) = 1 := by
    have : 2 * j + 2 = 2 * (j + 1) := by omega
    rw [this, pow_mul, neg_one_sq, one_pow]
  have harg : ((2 * j + 2 : ℕ) : ℝ) * Real.pi / (2 * (l : ℝ) + 1) =
      2 * Real.pi * ((j + 1 : ℕ) : ℝ) / (2 * (l : ℝ) + 1) := by
    push_cast
    ring
  rw [hpow, one_mul, harg]

private lemma dz_odd (l : ℕ) (δ : ℝ) (j : ℕ) (hj : j < l) :
    dz l δ (2 * j + 1) = -Real.pi - beta l δ (j + 1) - 2 * Real.pi := by
  have hsym := dz_symm l δ (2 * j + 1) (by omega)
  have hidx : 2 * l + 1 - (2 * j + 1) = 2 * (l - 1 - j) + 2 := by omega
  have hev := dz_even l δ (l - 1 - j)
  have hj2 : l - 1 - j + 1 = l + 1 - (j + 1) := by omega
  rw [hidx, hev, hj2] at hsym
  dsimp [beta]
  linarith

private noncomputable def xi (l : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  Real.pi / 2 + ∑ i ∈ Finset.Ico 1 k, dz l δ i

private lemma xi_one (l : ℕ) (δ : ℝ) : xi l δ 1 = Real.pi / 2 := by
  simp [xi]

private lemma xi_succ (l : ℕ) (δ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    xi l δ (k + 1) = xi l δ k + dz l δ k := by
  dsimp [xi]
  rw [Finset.sum_Ico_succ_top hk]
  ring

private lemma raw_seq_as_xi_prod (lam δ : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (l j : ℕ) (hj : j ≤ l) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      seqOp (sVec lam) tVec (alpha l δ) (beta l δ) j *ᵥ sVec lam =
        ω • ((R 0 (xi l δ 1 - xi l δ (2 * j + 1)) *
          Aprod (blochAngle lam) (xi l δ) (2 * j + 1)) *ᵥ tbarVec) := by
  induction j with
  | zero =>
    refine ⟨1, norm_one, ?_⟩
    have hprep := (rotation_identities lam hlam0 hlam1 0 0).1
    simp only [seqOp, Matrix.one_mulVec, one_smul, Nat.mul_zero, zero_add, sub_self,
      R0_zero, Matrix.one_mul, Aprod, Matrix.mul_one, xi_one]
    exact hprep.symm
  | succ j ih =>
    obtain ⟨ω, hω, hj_eq⟩ := ih (by omega)
    set αj := alpha l δ (j + 1)
    set βj := beta l δ (j + 1)
    set φ := blochAngle lam
    have hSs := (reflections_as_rotations lam hlam0 hlam1 αj βj).1
    have hSt := (reflections_as_rotations lam hlam0 hlam1 αj βj).2
    set c_step : ℂ :=
      Complex.exp (-((αj / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((βj / 2 : ℝ) : ℂ) * Complex.I)
    have hc_norm : ‖c_step * ω‖ = 1 := by
      have ha : ‖Complex.exp (-((αj / 2 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        have : -((αj / 2 : ℝ) : ℂ) * Complex.I = ((-(αj / 2) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      have hb : ‖Complex.exp (((βj / 2 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
        exact Complex.norm_exp_ofReal_mul_I (βj / 2)
      rw [norm_mul, norm_mul, ha, hb, hω, mul_one, mul_one]
    refine ⟨c_step * ω, hc_norm, ?_⟩
    have hG : G (sVec lam) tVec αj βj = (-c_step) • (R φ αj * R 0 βj) := by
      dsimp [G, c_step, φ]
      rw [hSs, hSt, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← neg_smul]
    set B : ℝ := βj + (xi l δ 1 - xi l δ (2 * j + 1))
    have hξ1 := xi_one l δ
    have hξ2 := xi_succ l δ (2 * j + 1) (by omega)
    have hξ3 := xi_succ l δ (2 * j + 2) (by omega)
    have hdz1 := dz_odd l δ j (by omega)
    have hdz2 := dz_even l δ j
    have hang1 : -Real.pi / 2 - B = xi l δ (2 * j + 2) + 2 * Real.pi := by
      dsimp [B, βj]; linarith
    have hang2 : Real.pi / 2 - αj - B = xi l δ (2 * j + 3) + 2 * Real.pi := by
      dsimp [B, αj, βj]; linarith
    have hang3 : αj + B = (xi l δ 1 - xi l δ (2 * j + 3)) - 2 * Real.pi := by
      dsimp [B, αj, βj]; linarith
    have hmat : R φ αj * R 0 βj * R 0 (xi l δ 1 - xi l δ (2 * j + 1)) =
        (-1 : ℂ) • (R 0 (xi l δ 1 - xi l δ (2 * j + 3)) *
          A φ (xi l δ (2 * j + 3)) * A φ (xi l δ (2 * j + 2))) := by
      calc R φ αj * R 0 βj * R 0 (xi l δ 1 - xi l δ (2 * j + 1))
        _ = R φ αj * (R 0 βj * R 0 (xi l δ 1 - xi l δ (2 * j + 1))) := by
            rw [Matrix.mul_assoc]
        _ = R φ αj * R 0 B := by
            rw [R0_add]
        _ = R 0 (αj + B) * A φ (Real.pi / 2 - αj - B) * A φ (-Real.pi / 2 - B) := by
            exact Rφ_mul_R0 lam hlam0 hlam1 αj B
        _ = (-1 : ℂ) • (R 0 (xi l δ 1 - xi l δ (2 * j + 3)) *
              A φ (xi l δ (2 * j + 3)) * A φ (xi l δ (2 * j + 2))) := by
            rw [hang1, hang2, hang3, A_add_two_pi, A_add_two_pi, R0_sub_two_pi]
            simp only [Matrix.smul_mul]
    simp only [seqOp, ← Matrix.mulVec_mulVec]
    rw [hj_eq, Matrix.mulVec_smul, hG, Matrix.smul_mulVec, smul_smul,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc (R φ αj * R 0 βj), hmat]
    have hidx2 : 2 * j + 1 + 1 = 2 * j + 2 := by omega
    have hidx3 : 2 * (j + 1) + 1 = 2 * j + 2 + 1 := by omega
    rw [hidx3, Aprod, hidx2, Aprod]
    simp only [Matrix.smul_mul, Matrix.smul_mulVec, smul_smul, Matrix.mul_assoc,
      Matrix.mulVec_mulVec]
    congr 1
    ring

private lemma R0_mul_Aprod (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (ζ : ℕ → ℝ) (ψ : ℝ) (h : ℕ) :
    R 0 ψ * Aprod (blochAngle lam) ζ h =
      Aprod (blochAngle lam) (fun k => ζ k + ψ) h * R 0 ψ := by
  induction h with
  | zero =>
    simp [Aprod]
  | succ h ih =>
    calc R 0 ψ * Aprod (blochAngle lam) ζ (h + 1)
      _ = (R 0 ψ * A (blochAngle lam) (ζ (h + 1))) * Aprod (blochAngle lam) ζ h := by
          simp [Aprod, Matrix.mul_assoc]
      _ = A (blochAngle lam) (ζ (h + 1) + ψ) * (R 0 ψ * Aprod (blochAngle lam) ζ h) := by
          rw [R0_mul_A lam h0 h1, Matrix.mul_assoc]
      _ = Aprod (blochAngle lam) (fun k => ζ k + ψ) (h + 1) * R 0 ψ := by
          rw [ih]
          simp [Aprod, Matrix.mul_assoc]

private lemma R0_mulVec_tbarVec (θ : ℝ) :
    R 0 θ *ᵥ tbarVec = Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) • tbarVec := by
  rw [R0_eq θ]
  ext i
  fin_cases i <;> simp [tbarVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma zeta_succ (l : ℕ) (δ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    zeta l δ (k + 1) = zeta l δ k + dz l δ k := by
  dsimp [zeta]
  rw [Finset.sum_Ico_succ_top hk]
  ring

private lemma zeta_palindrome_diff (l : ℕ) (δ : ℝ) (m : ℕ) (hm : m ≤ l) :
    zeta l δ (l + 1 - m) = zeta l δ (l + 1 + m) + (m : ℝ) * (2 * Real.pi) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have ihm := ih (by omega)
    have h1 : zeta l δ (l + 1 - m) = zeta l δ (l - m) + dz l δ (l - m) := by
      have hidx : l + 1 - m = (l - m) + 1 := by omega
      rw [hidx, zeta_succ l δ (l - m) (by omega)]
    have h2 : zeta l δ (l + 1 + (m + 1)) = zeta l δ (l + 1 + m) + dz l δ (l + 1 + m) := by
      have hidx : l + 1 + (m + 1) = (l + 1 + m) + 1 := by omega
      rw [hidx, zeta_succ l δ (l + 1 + m) (by omega)]
    have h3 : dz l δ (l - m) = -dz l δ (l + 1 + m) - 2 * Real.pi := by
      have hidx : l - m = 2 * l + 1 - (l + 1 + m) := by omega
      rw [hidx, dz_symm l δ (l + 1 + m) (by omega)]
    have hsub : l + 1 - (m + 1) = l - m := by omega
    rw [hsub]
    push_cast
    linarith

private lemma exp_add_nat_mul_two_pi (x : ℝ) (m : ℕ) :
    Complex.exp (((x + (m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((x : ℂ) * Complex.I) := by
  have h : ((x + (m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I =
      (x : ℂ) * Complex.I + (m : ℕ) * ((2 * Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]

theorem solution (lam δ : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (l : ℕ) :
    (∃ ω : ℂ, ‖ω‖ = 1 ∧ ∃ θ : ℝ,
      seqOp (sVec lam) tVec (alpha l δ) (beta l δ) l *ᵥ sVec lam =
        ω • ((R 0 θ * Aprod (blochAngle lam) (zeta l δ) (2 * l + 1)) *ᵥ tbarVec)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 2 * l + 1 →
      Complex.exp ((zeta l δ k : ℂ) * Complex.I) =
        Complex.exp ((zeta l δ (2 * l + 2 - k) : ℂ) * Complex.I)) := by
  constructor
  · obtain ⟨ω, hω, hseq⟩ := raw_seq_as_xi_prod lam δ hlam0.le hlam1 l l (le_refl l)
    set ψ : ℝ := Real.pi / 2 - (-1 : ℝ) ^ l * Real.pi / 2 +
      ∑ i ∈ Finset.Ico 1 (l + 1), dz l δ i
    have hxi_eq : xi l δ = fun k => zeta l δ k + ψ := by
      ext k
      dsimp [xi, zeta, ψ]
      ring
    have hAprod : Aprod (blochAngle lam) (xi l δ) (2 * l + 1) =
        R 0 ψ * Aprod (blochAngle lam) (zeta l δ) (2 * l + 1) * R 0 (-ψ) := by
      calc Aprod (blochAngle lam) (xi l δ) (2 * l + 1)
        _ = Aprod (blochAngle lam) (fun k => zeta l δ k + ψ) (2 * l + 1) * 1 := by
            rw [hxi_eq, Matrix.mul_one]
        _ = Aprod (blochAngle lam) (fun k => zeta l δ k + ψ) (2 * l + 1) *
              (R 0 ψ * R 0 (-ψ)) := by
            rw [R0_mul_neg_self]
        _ = (Aprod (blochAngle lam) (fun k => zeta l δ k + ψ) (2 * l + 1) * R 0 ψ) *
              R 0 (-ψ) := by
            rw [← Matrix.mul_assoc]
        _ = R 0 ψ * Aprod (blochAngle lam) (zeta l δ) (2 * l + 1) * R 0 (-ψ) := by
            rw [← R0_mul_Aprod lam hlam0.le hlam1 (zeta l δ) ψ (2 * l + 1)]
    set eψ : ℂ := Complex.exp (-((-ψ / 2 : ℝ) : ℂ) * Complex.I)
    have heψ : ‖eψ‖ = 1 := by
      dsimp [eψ]
      have : -((-ψ / 2 : ℝ) : ℂ) * Complex.I = ((ψ / 2 : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    refine ⟨ω * eψ, by rw [norm_mul, hω, heψ, mul_one],
      (xi l δ 1 - xi l δ (2 * l + 1)) + ψ, ?_⟩
    rw [hseq, hAprod]
    calc ω • ((R 0 (xi l δ 1 - xi l δ (2 * l + 1)) *
          (R 0 ψ * Aprod (blochAngle lam) (zeta l δ) (2 * l + 1) * R 0 (-ψ))) *ᵥ tbarVec)
      _ = ω • (((R 0 (xi l δ 1 - xi l δ (2 * l + 1)) * R 0 ψ) *
            Aprod (blochAngle lam) (zeta l δ) (2 * l + 1)) *ᵥ (R 0 (-ψ) *ᵥ tbarVec)) := by
          simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = (ω * eψ) • ((R 0 ((xi l δ 1 - xi l δ (2 * l + 1)) + ψ) *
            Aprod (blochAngle lam) (zeta l δ) (2 * l + 1)) *ᵥ tbarVec) := by
          rw [R0_add, R0_mulVec_tbarVec (-ψ), Matrix.mulVec_smul, smul_smul]
  · intro k hk1 hk2
    rcases le_or_gt k (l + 1) with hle | hgt
    · set m := l + 1 - k
      have hm : m ≤ l := by omega
      have hk_eq : k = l + 1 - m := by omega
      have hsym_eq : 2 * l + 2 - k = l + 1 + m := by omega
      rw [hsym_eq, hk_eq, zeta_palindrome_diff l δ m hm, exp_add_nat_mul_two_pi]
    · set m := k - (l + 1)
      have hm : m ≤ l := by omega
      have hk_eq : k = l + 1 + m := by omega
      have hsym_eq : 2 * l + 2 - k = l + 1 - m := by omega
      rw [hsym_eq, hk_eq, zeta_palindrome_diff l δ m hm, exp_add_nat_mul_two_pi]
