-- Prove2me | solution 1 for BosonicLearn.occupation_family
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:12:24.522131+00:00
-- url     : https://prove2.me/submissions/7f0b06a8-3445-4d6e-8c7f-292b8272f2f3

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_IsPassive
import Definitions.Def_BosonicLearn_promiseClass
import Theorems.Thm_BosonicLearn_fugacity_isGaussianState
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Theorems.Thm_BosonicLearn_fugacity_promiseClass

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-! ### Functional calculus in a fixed unitary eigenbasis -/

/-- `U diag(a) Uᴴ` for a real diagonal `a`. -/
private def cj {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  U * Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)) * Uᴴ

private lemma cj_one {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1) :
    cj U (fun _ => 1) = 1 := by
  simp only [cj, Complex.ofReal_one, Matrix.diagonal_one, Matrix.mul_one, hU2]

private lemma cj_add {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℝ) :
    cj U a + cj U b = cj U (fun i => a i + b i) := by
  simp only [cj, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add, Complex.ofReal_add]

private lemma cj_sub {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℝ) :
    cj U a - cj U b = cj U (fun i => a i - b i) := by
  simp only [cj, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub, Complex.ofReal_sub]

private lemma cj_smul {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (a : Fin n → ℝ) :
    ((c : ℝ) : ℂ) • cj U a = cj U (fun i => c * a i) := by
  unfold cj
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
  congr 3
  funext i
  simp

private lemma cj_mul {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1)
    (a b : Fin n → ℝ) : cj U a * cj U b = cj U (fun i => a i * b i) := by
  unfold cj
  have h : U * Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)) * Uᴴ *
      (U * Matrix.diagonal (fun i => ((b i : ℝ) : ℂ)) * Uᴴ) =
      U * (Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)) *
        ((Uᴴ * U) * Matrix.diagonal (fun i => ((b i : ℝ) : ℂ)))) * Uᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, hU1, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
  simp only [Complex.ofReal_mul]

private lemma cj_inv {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1)
    (hU2 : U * Uᴴ = 1) (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    (cj U a)⁻¹ = cj U (fun i => (a i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [cj_mul U hU1, ← cj_one U hU2]
  congr 1
  funext i
  exact mul_inv_cancel₀ (ha i)

private lemma cj_psd {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) : (cj U a).PosSemidef := by
  unfold cj
  exact (Matrix.PosSemidef.diagonal
    (fun i => Complex.zero_le_real.mpr (ha i))).mul_mul_conjTranspose_same U

private lemma cj_pd {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) : (cj U a).PosDef := by
  unfold cj
  refine (Matrix.PosDef.diagonal
    (fun i => Complex.zero_lt_real.mpr (ha i))).mul_mul_conjTranspose_same ?_
  rw [Matrix.vecMul_injective_iff_isUnit]
  exact (Matrix.isUnit_iff_isUnit_det U).mpr (Matrix.isUnit_det_of_left_inverse hU1)

private lemma cj_nonneg {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU1 : Uᴴ * U = 1)
    (a : Fin n → ℝ) (h : (cj U a).PosSemidef) : ∀ i, 0 ≤ a i := by
  have h2 := h.conjTranspose_mul_mul_same U
  have e : Uᴴ * cj U a * U = Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)) := by
    unfold cj
    have h' : Uᴴ * (U * Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)) * Uᴴ) * U =
        (Uᴴ * U) * Matrix.diagonal (fun i => ((a i : ℝ) : ℂ)) * (Uᴴ * U) := by
      simp only [Matrix.mul_assoc]
    rw [h', hU1, Matrix.one_mul, Matrix.mul_one]
  rw [e, Matrix.posSemidef_diagonal_iff] at h2
  intro i
  exact Complex.zero_le_real.mp (h2 i)

private lemma cj_det {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU2 : U * Uᴴ = 1)
    (a : Fin n → ℝ) : (cj U a).det = ((∏ i, a i : ℝ) : ℂ) := by
  unfold cj
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul, hU2,
    Matrix.det_one, one_mul, Complex.ofReal_prod]

/-- Unitary diagonalization of a Hermitian matrix. -/
private lemma diag_data {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ D = cj U e := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hD.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  have hspec : D = V * Matrix.diagonal (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
    have h := hD.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  exact ⟨V, hD.eigenvalues, hV1, hV2, hspec⟩

/-! ### Scalar inequalities -/

private lemma sc_N (m ξ x : ℝ) (hm : 1 ≤ m) (hξ0 : 0 < ξ) (hξ : ξ ≤ 1 / 32) (hx1 : -4 ≤ x)
    (hx2 : x ≤ 4) : 7 / 8 * m ≤ m * (1 + ξ * x) ∧ m * (1 + ξ * x) ≤ 9 / 8 * m := by
  have h1 : -(1 / 8) ≤ ξ * x := by nlinarith
  have h2 : ξ * x ≤ 1 / 8 := by nlinarith
  constructor <;> nlinarith

private lemma sc_D (m N : ℝ) (hm : 1 ≤ m) (h1 : 7 / 8 * m ≤ N) (h2 : N ≤ 9 / 8 * m) :
    63 / 64 * m ^ 2 ≤ m + 2 * m * N - N ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

private lemma sc_sq (m N : ℝ) (hm : 1 ≤ m) (h1 : 7 / 8 * m ≤ N) (h2 : N ≤ 9 / 8 * m) :
    0 < m / (1 + m) * 1 - N * (1 + N)⁻¹ * (N * (1 + N)⁻¹) := by
  have hN : 0 < 1 + N := by nlinarith
  have hm1 : 0 < 1 + m := by linarith
  have hD : 0 < m + 2 * m * N - N ^ 2 := by
    have := sc_D m N hm h1 h2
    nlinarith
  have e : m / (1 + m) * 1 - N * (1 + N)⁻¹ * (N * (1 + N)⁻¹) =
      (m + 2 * m * N - N ^ 2) / ((1 + m) * (1 + N) ^ 2) := by
    field_simp
    ring
  rw [e]
  positivity

private lemma sc_mono (ν N : ℝ) (hν : 0 < ν) (h : ν ≤ N) :
    0 ≤ N * (1 + N)⁻¹ - ν / (1 + ν) * 1 := by
  have hN : 0 < 1 + N := by linarith
  have hν1 : 0 < 1 + ν := by linarith
  have e : N * (1 + N)⁻¹ - ν / (1 + ν) * 1 = (N - ν) / ((1 + N) * (1 + ν)) := by
    field_simp
    ring
  rw [e]
  exact div_nonneg (by linarith) (by positivity)

private lemma sc_renyi (m ξ x : ℝ) (hm : 1 ≤ m) (hξ0 : 0 < ξ) (hξ : ξ ≤ 1 / 32) (hx1 : -4 ≤ x)
    (hx2 : x ≤ 4) (N : ℝ) (hNdef : N = m * (1 + ξ * x)) :
    0 ≤ (1 - N * (1 + N)⁻¹) ^ 2 /
        ((1 - m / (1 + m)) * (1 - (m / (1 + m))⁻¹ * (N * (1 + N)⁻¹ * (N * (1 + N)⁻¹)))) ∧
    (1 - N * (1 + N)⁻¹) ^ 2 /
        ((1 - m / (1 + m)) * (1 - (m / (1 + m))⁻¹ * (N * (1 + N)⁻¹ * (N * (1 + N)⁻¹)))) ≤
      Real.exp (21 * ξ ^ 2) := by
  obtain ⟨h1, h2⟩ := sc_N m ξ x hm hξ0 hξ hx1 hx2
  rw [← hNdef] at h1 h2
  have hN : 0 < 1 + N := by nlinarith
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < 1 + m := by linarith
  have hDlow := sc_D m N hm h1 h2
  have hD : 0 < m + 2 * m * N - N ^ 2 := by nlinarith
  have e : (1 - N * (1 + N)⁻¹) ^ 2 /
        ((1 - m / (1 + m)) * (1 - (m / (1 + m))⁻¹ * (N * (1 + N)⁻¹ * (N * (1 + N)⁻¹)))) =
      (m + m ^ 2) / (m + 2 * m * N - N ^ 2) := by
    have e1 : 1 - N * (1 + N)⁻¹ = (1 + N)⁻¹ := by
      field_simp
      ring
    have e2 : 1 - m / (1 + m) = (1 + m)⁻¹ := by
      field_simp
      ring
    have e3 : 1 - (m / (1 + m))⁻¹ * (N * (1 + N)⁻¹ * (N * (1 + N)⁻¹)) =
        (m + 2 * m * N - N ^ 2) / (m * (1 + N) ^ 2) := by
      field_simp
      ring
    rw [e1, e2, e3]
    field_simp
  rw [e]
  refine ⟨div_nonneg (by positivity) hD.le, ?_⟩
  have hx2' : x ^ 2 ≤ 16 := by nlinarith
  have hNm : (N - m) ^ 2 ≤ 16 * m ^ 2 * ξ ^ 2 := by
    have : (N - m) ^ 2 = m ^ 2 * ξ ^ 2 * x ^ 2 := by rw [hNdef]; ring
    rw [this]
    nlinarith [mul_nonneg (sq_nonneg m) (sq_nonneg ξ)]
  have hkey : (m + m ^ 2) / (m + 2 * m * N - N ^ 2) ≤ 21 * ξ ^ 2 + 1 := by
    rw [div_le_iff₀ hD]
    have h3 : 16 * m ^ 2 * ξ ^ 2 ≤ 21 * ξ ^ 2 * (m + 2 * m * N - N ^ 2) := by
      have : 16 * m ^ 2 ≤ 21 * (m + 2 * m * N - N ^ 2) := by nlinarith
      nlinarith [sq_nonneg ξ]
    nlinarith
  exact hkey.trans (Real.add_one_le_exp _)

/-! ### The theorem -/

theorem solution {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (h4 : (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef)
    (h4' : (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef)
    (m ξ : ℝ) (hm : 1 ≤ m) (hξ0 : 0 < ξ) (hξ : ξ ≤ 1 / 32)
    (Nm R : Matrix (Fin n) (Fin n) ℂ)
    (hN : Nm = ((m : ℝ) : ℂ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + ((ξ : ℝ) : ℂ) • X))
    (hRdef : R = Nm * (1 + Nm)⁻¹) :
    (Nm - ((7 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
    (((9 / 8 * m : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Nm).PosSemidef ∧
    R.PosSemidef ∧ (1 - R).PosDef ∧
    (((m / (1 + m) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R * R).PosDef ∧
    (∀ ν : ℝ, 0 < ν → ν ≤ 7 / 8 * m →
      ∃ ρ : State (Occupation (Fin n)), ρ.coefficients = fugacityCoeff R ∧ IsPassive ρ ∧
        ρ ∈ promiseClass n ν) ∧
    (1 - R).det.re ^ 2 /
        ((1 - m / (1 + m)) ^ n * (1 - (((m / (1 + m))⁻¹ : ℝ) : ℂ) • (R * R)).det.re) ≤
      Real.exp (21 * ξ ^ 2 * n) := by
  obtain ⟨U, x, hU1, hU2, hXe⟩ := diag_data X hX
  -- the eigenvalues of `X` lie in `[-4, 4]`
  have hx2 : ∀ i, x i ≤ 4 := by
    have h : (cj U (fun i => 4 * 1 - x i)).PosSemidef := by
      rw [← cj_sub, ← cj_smul, cj_one U hU2, ← hXe]
      exact h4
    intro i
    have := cj_nonneg U hU1 _ h i
    linarith
  have hx1 : ∀ i, -4 ≤ x i := by
    have h : (cj U (fun i => 4 * 1 + x i)).PosSemidef := by
      rw [← cj_add, ← cj_smul, cj_one U hU2, ← hXe]
      exact h4'
    intro i
    have := cj_nonneg U hU1 _ h i
    linarith
  -- the eigenvalues of `Nm`
  obtain ⟨N, hNdef⟩ : ∃ N : Fin n → ℝ, N = fun i => m * (1 + ξ * x i) := ⟨_, rfl⟩
  have hNi : ∀ i, N i = m * (1 + ξ * x i) := fun i => by rw [hNdef]
  have hNm : Nm = cj U N := by
    rw [hNdef, hN, hXe, ← cj_one U hU2, cj_smul, cj_add, cj_smul]
  have hNb : ∀ i, 7 / 8 * m ≤ N i ∧ N i ≤ 9 / 8 * m := fun i => by
    rw [hNi i]
    exact sc_N m ξ (x i) hm hξ0 hξ (hx1 i) (hx2 i)
  have h1N : ∀ i, 0 < 1 + N i := fun i => by
    have := (hNb i).1
    linarith
  -- the eigenvalues of `R`
  obtain ⟨r, hrdef⟩ : ∃ r : Fin n → ℝ, r = fun i => N i * (1 + N i)⁻¹ := ⟨_, rfl⟩
  have hri : ∀ i, r i = N i * (1 + N i)⁻¹ := fun i => by rw [hrdef]
  have hR : R = cj U r := by
    rw [hrdef, hRdef, hNm, ← cj_one U hU2, cj_add, cj_inv U hU1 hU2 _ (fun i => (h1N i).ne'),
      cj_mul U hU1]
  have hr0 : ∀ i, 0 ≤ r i := fun i => by
    rw [hri i]
    have := (hNb i).1
    exact mul_nonneg (by linarith) (inv_nonneg.mpr (h1N i).le)
  have h1r : ∀ i, 1 - r i = (1 + N i)⁻¹ := fun i => by
    rw [hri i]
    have := (h1N i).ne'
    field_simp
    ring
  have h1R : 1 - R = cj U (fun i => 1 - r i) := by
    rw [hR, ← cj_one U hU2, cj_sub]
  have hRpsd : R.PosSemidef := by
    rw [hR]
    exact cj_psd U r hr0
  have hR1pd : (1 - R).PosDef := by
    rw [h1R]
    exact cj_pd U hU1 _ (fun i => by rw [h1r i]; exact inv_pos.mpr (h1N i))
  refine ⟨?_, ?_, hRpsd, hR1pd, ?_, ?_, ?_⟩
  · rw [hNm, ← cj_one U hU2, cj_smul, cj_sub]
    exact cj_psd U _ (fun i => by have := (hNb i).1; linarith)
  · rw [hNm, ← cj_one U hU2, cj_smul, cj_sub]
    exact cj_psd U _ (fun i => by have := (hNb i).2; linarith)
  · rw [hR, cj_mul U hU1, ← cj_one U hU2, cj_smul, cj_sub]
    exact cj_pd U hU1 _ (fun i => by
      rw [hri i]
      exact sc_sq m (N i) hm (hNb i).1 (hNb i).2)
  · intro ν hν0 hν
    have hRν : (R - ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
      rw [hR, ← cj_one U hU2, cj_smul, cj_sub]
      exact cj_psd U _ (fun i => by
        rw [hri i]
        exact sc_mono ν (N i) hν0 (hν.trans (hNb i).1))
    obtain ⟨ρ, hρ, hG⟩ := fugacity_isGaussianState R hRpsd hR1pd
    refine ⟨ρ, hρ, ⟨⟨0, _, hG⟩, fun u v huv => ?_⟩,
      fugacity_promiseClass R hRpsd hR1pd ν hν0 hRν ρ hρ⟩
    rw [hρ]
    show (1 - R).det • gammaFock R u v = 0
    rw [(gammaFock_basic R u v).1 huv, smul_zero]
  · have hdet1 : (1 - R).det.re = ∏ i, (1 - r i) := by
      rw [h1R, cj_det U hU2, Complex.ofReal_re]
    have hdet2 : (1 - (((m / (1 + m))⁻¹ : ℝ) : ℂ) • (R * R)).det.re =
        ∏ i, (1 - (m / (1 + m))⁻¹ * (r i * r i)) := by
      rw [hR, cj_mul U hU1, cj_smul, ← cj_one U hU2, cj_sub, cj_det U hU2, Complex.ofReal_re]
    have hconst : (1 - m / (1 + m)) ^ n = ∏ _i : Fin n, (1 - m / (1 + m)) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hdet1, hdet2, hconst, ← Finset.prod_pow, ← Finset.prod_mul_distrib,
      ← Finset.prod_div_distrib]
    have hfac : ∀ i, 0 ≤ (1 - r i) ^ 2 /
          ((1 - m / (1 + m)) * (1 - (m / (1 + m))⁻¹ * (r i * r i))) ∧
        (1 - r i) ^ 2 / ((1 - m / (1 + m)) * (1 - (m / (1 + m))⁻¹ * (r i * r i))) ≤
          Real.exp (21 * ξ ^ 2) := fun i => by
      rw [hri i]
      exact sc_renyi m ξ (x i) hm hξ0 hξ (hx1 i) (hx2 i) (N i) (hNi i)
    calc ∏ i, (1 - r i) ^ 2 / ((1 - m / (1 + m)) * (1 - (m / (1 + m))⁻¹ * (r i * r i)))
        ≤ ∏ _i : Fin n, Real.exp (21 * ξ ^ 2) :=
          Finset.prod_le_prod (fun i _ => (hfac i).1) (fun i _ => (hfac i).2)
      _ = Real.exp (21 * ξ ^ 2 * n) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          congr 1
          ring
