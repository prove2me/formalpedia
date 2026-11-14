-- Prove2me | solution 1 for BosonicLearn.fugacity_isGaussianState
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:48:19.1962+00:00
-- url     : https://prove2.me/submissions/752264c7-8c8e-499a-8b91-a9bd77de50cd

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_IsGaussianState
import Theorems.Thm_BosonicLearn_fugacityCoeff_isDensity
import Theorems.Thm_BosonicLearn_fugacity_characteristic
import Theorems.Thm_BosonicLearn_fugacity_photon_number

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open scoped ENNReal Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-! ### The covariance matrix in interleaved coordinates -/

/-- The interleaved covariance `γ = 2Σ` of the statement, for a complex matrix `C`. -/
private def gam {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) : OscillatorCovariance (Fin n) :=
  fun a b => 2 * ((1 / 2 : ℝ) • Matrix.fromBlocks (C.map Complex.re) (-(C.map Complex.im))
      (C.map Complex.im) (C.map Complex.re))
    (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1) (if b.2 = 0 then Sum.inl b.1 else Sum.inr b.1)

private lemma gam_apply {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (j k : Fin n) :
    gam C (j, 0) (k, 0) = (C j k).re ∧ gam C (j, 0) (k, 1) = -(C j k).im ∧
    gam C (j, 1) (k, 0) = (C j k).im ∧ gam C (j, 1) (k, 1) = (C j k).re := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [gam, Matrix.smul_apply]

private lemma varianceForm_gam {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (ξ : InterleavedQuadrature (Fin n) → ℝ) :
    varianceForm (gam C) ξ = ∑ j, ∑ k, (ξ (j, 0) * (C j k).re * ξ (k, 0) - ξ (j, 0) * (C j k).im * ξ (k, 1)
      + ξ (j, 1) * (C j k).im * ξ (k, 0) + ξ (j, 1) * (C j k).re * ξ (k, 1)) := by
  unfold varianceForm
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  obtain ⟨h00, h01, h10, h11⟩ := gam_apply C j k
  rw [h00, h01, h10, h11]
  ring

private lemma varianceForm_smul {n : ℕ} (γ : OscillatorCovariance (Fin n))
    (ξ : InterleavedQuadrature (Fin n) → ℝ) (t : ℝ) :
    varianceForm γ (t • ξ) = t ^ 2 * varianceForm γ ξ := by
  unfold varianceForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The Hermitian form `ζ† C ζ` at `ζ = (−ξ_p + i ξ_q)/√2` is half of the real quadratic form of `γ`. -/
private lemma quad_eq {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.IsHermitian)
    (ξ : InterleavedQuadrature (Fin n) → ℝ) :
    ∑ j, ∑ k, star ((-(ξ (j, 1) : ℂ) + Complex.I * (ξ (j, 0) : ℂ)) / (Real.sqrt 2 : ℂ)) * C j k *
        ((-(ξ (k, 1) : ℂ) + Complex.I * (ξ (k, 0) : ℂ)) / (Real.sqrt 2 : ℂ)) =
      ((varianceForm (gam C) ξ / 2 : ℝ) : ℂ) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  -- each term in the form `A * C j k`
  have hterm : ∀ j k : Fin n,
      star ((-(ξ (j, 1) : ℂ) + Complex.I * (ξ (j, 0) : ℂ)) / (Real.sqrt 2 : ℂ)) * C j k *
        ((-(ξ (k, 1) : ℂ) + Complex.I * (ξ (k, 0) : ℂ)) / (Real.sqrt 2 : ℂ)) =
      ((((ξ (j, 1) * ξ (k, 1) + ξ (j, 0) * ξ (k, 0)) / 2 : ℝ) : ℂ) +
        (((ξ (j, 0) * ξ (k, 1) - ξ (j, 1) * ξ (k, 0)) / 2 : ℝ) : ℂ) * Complex.I) * C j k := by
    intro j k
    rw [div_eq_mul_inv, div_eq_mul_inv, star_mul', star_inv₀]
    simp only [star_add, star_neg, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    have e : (-(ξ (j, 1) : ℂ) + -Complex.I * (ξ (j, 0) : ℂ)) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * C j k *
        ((-(ξ (k, 1) : ℂ) + Complex.I * (ξ (k, 0) : ℂ)) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) =
        (-(ξ (j, 1) : ℂ) + -Complex.I * (ξ (j, 0) : ℂ)) * (-(ξ (k, 1) : ℂ) + Complex.I * (ξ (k, 0) : ℂ)) *
          C j k * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by ring
    rw [e, h2]
    push_cast
    linear_combination (-(ξ (j, 0) : ℂ) * (ξ (k, 0) : ℂ) * C j k * 2⁻¹) * Complex.I_sq
  set Q : ℂ := ∑ j, ∑ k, star ((-(ξ (j, 1) : ℂ) + Complex.I * (ξ (j, 0) : ℂ)) / (Real.sqrt 2 : ℂ)) * C j k *
        ((-(ξ (k, 1) : ℂ) + Complex.I * (ξ (k, 0) : ℂ)) / (Real.sqrt 2 : ℂ)) with hQ
  -- `Q` is real
  have hstar : star Q = Q := by
    rw [hQ, star_sum]
    simp only [star_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have hCkj : star (C k j) = C j k := by
      have := congrFun (congrFun hC.eq j) k
      simpa [Matrix.conjTranspose_apply] using this
    rw [star_mul', star_mul', star_star, hCkj]
    ring
  have him : Q.im = 0 := by
    have := Complex.conj_eq_iff_im.mp hstar
    exact this
  have hre : Q.re = varianceForm (gam C) ξ / 2 := by
    rw [hQ, Complex.re_sum, varianceForm_gam, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm j k, Complex.mul_re]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
    ring
  apply Complex.ext
  · rw [hre, Complex.ofReal_re]
  · rw [him, Complex.ofReal_im]

/-! ### The statement -/

theorem solution {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) :
    ∃ ρ : State (Occupation (Fin n)), ρ.coefficients = fugacityCoeff R ∧
      IsGaussianState ρ 0 ((1 / 2 : ℝ) • Matrix.fromBlocks
        (((1 + R) * (1 - R)⁻¹).map Complex.re) (-(((1 + R) * (1 - R)⁻¹).map Complex.im))
        (((1 + R) * (1 - R)⁻¹).map Complex.im) (((1 + R) * (1 - R)⁻¹).map Complex.re)) := by
  -- `C = (1 + R)(1 − R)⁻¹ = 2 (1 − R)⁻¹ − 1` is Hermitian
  have hunit : IsUnit (1 - R).det := (Matrix.isUnit_iff_isUnit_det _).mp hR1.isUnit
  have hCeq : (1 + R) * (1 - R)⁻¹ = (2 : ℂ) • (1 - R)⁻¹ - 1 := by
    have h1 : (1 + R) = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (1 - R) := by
      rw [two_smul]; abel
    rw [h1, Matrix.sub_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.smul_mul, Matrix.one_mul]
  have hinv : ((1 - R)⁻¹).IsHermitian := hR1.isHermitian.inv
  have hC : ((1 + R) * (1 - R)⁻¹).IsHermitian := by
    rw [hCeq]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hinv.eq]
    simp
  set C : Matrix (Fin n) (Fin n) ℂ := (1 + R) * (1 - R)⁻¹ with hCdef
  obtain ⟨hsum, hchar⟩ := fugacity_characteristic R hR hR1
  refine ⟨⟨fugacityCoeff R, fugacityCoeff_isDensity R hR hR1⟩, rfl, ?_⟩
  unfold IsGaussianState
  show GaussianAt (fugacityCoeff R)
    (fun a => (0 : Fin n ⊕ Fin n → ℝ) (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)) (gam C)
  have hmean : ∀ ξ : InterleavedQuadrature (Fin n) → ℝ,
      meanForm (fun a => (0 : Fin n ⊕ Fin n → ℝ) (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)) ξ = 0 := by
    intro ξ
    simp [meanForm]
  -- the characteristic function
  have hχ : ∀ ξ : InterleavedQuadrature (Fin n) → ℝ, oscillatorCharacteristic (fugacityCoeff R) ξ =
      ((Real.exp (-(varianceForm (gam C) ξ) / 4) : ℝ) : ℂ) := by
    intro ξ
    rw [hchar ξ, quad_eq C hC ξ, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hχt : ∀ (ξ : InterleavedQuadrature (Fin n) → ℝ) (t : ℝ),
      oscillatorCharacteristic (fugacityCoeff R) (t • ξ) =
        ((Real.exp (-(t ^ 2 * varianceForm (gam C) ξ) / 4) : ℝ) : ℂ) := by
    intro ξ t
    rw [hχ, varianceForm_smul]
  refine ⟨⟨?_, ?_, hsum, ?_⟩, ?_⟩
  · -- finite energy
    unfold photonEnergy
    rw [fugacity_photon_number R hR hR1]
    exact ENNReal.ofReal_lt_top
  · -- symmetry
    apply Matrix.ext
    rintro ⟨j, s⟩ ⟨k, s'⟩
    have hCkj : C k j = star (C j k) := by
      have := congrFun (congrFun hC.eq j) k
      rw [Matrix.conjTranspose_apply] at this
      rw [← this, star_star]
    have hre : (C k j).re = (C j k).re := by rw [hCkj]; simp
    have him : (C k j).im = -(C j k).im := by rw [hCkj]; simp
    obtain ⟨h00, h01, h10, h11⟩ := gam_apply C j k
    obtain ⟨g00, g01, g10, g11⟩ := gam_apply C k j
    rw [Matrix.transpose_apply]
    fin_cases s <;> fin_cases s'
    · show gam C (k, 0) (j, 0) = gam C (j, 0) (k, 0)
      rw [g00, h00, hre]
    · show gam C (k, 1) (j, 0) = gam C (j, 0) (k, 1)
      rw [g10, h01, him]
    · show gam C (k, 0) (j, 1) = gam C (j, 1) (k, 0)
      rw [g01, h10, him, neg_neg]
    · show gam C (k, 1) (j, 1) = gam C (j, 1) (k, 1)
      rw [g11, h11, hre]
  · -- first and second derivatives of the characteristic function
    intro ξ
    set q : ℝ := varianceForm (gam C) ξ with hq
    have hfun : (fun t : ℝ => oscillatorCharacteristic (fugacityCoeff R) (t • ξ)) =
        fun t : ℝ => ((Real.exp (-(t ^ 2 * q) / 4) : ℝ) : ℂ) := funext fun t => hχt ξ t
    have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2 * q) / 4))
        (Real.exp (-(t ^ 2 * q) / 4) * (-(t * q) / 2)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 * q) / 4) (-(t * q) / 2) t := by
        have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
          simpa using hasDerivAt_pow 2 t
        have h3 := (h2.mul_const q).neg.div_const 4
        have e : -(2 * t * q) / 4 = -(t * q) / 2 := by ring
        rw [e] at h3
        exact h3
      exact (Real.hasDerivAt_exp _).comp t h1
    have hdc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((Real.exp (-(t ^ 2 * q) / 4) : ℝ) : ℂ))
        ((Real.exp (-(t ^ 2 * q) / 4) * (-(t * q) / 2) : ℝ) : ℂ) t := fun t => (hd t).ofReal_comp
    have hderiv : deriv (fun t : ℝ => ((Real.exp (-(t ^ 2 * q) / 4) : ℝ) : ℂ)) =
        fun t : ℝ => ((Real.exp (-(t ^ 2 * q) / 4) * (-(t * q) / 2) : ℝ) : ℂ) :=
      funext fun t => (hdc t).deriv
    rw [hfun, hderiv, hmean ξ]
    constructor
    · have h := hdc 0
      have e : ((Real.exp (-((0 : ℝ) ^ 2 * q) / 4) * (-((0 : ℝ) * q) / 2) : ℝ) : ℂ) =
          Complex.I * ((0 : ℝ) : ℂ) := by simp
      rw [e] at h
      exact h
    · have h3 : HasDerivAt (fun t : ℝ => -(t * q) / 2) (-q / 2) 0 := by
        have h4 := ((hasDerivAt_id (0 : ℝ)).mul_const q).neg.div_const 2
        have e : -(1 * q) / 2 = -q / 2 := by ring
        rw [e] at h4
        exact h4
      have h2 := (hd 0).mul h3
      have e : Real.exp (-((0 : ℝ) ^ 2 * q) / 4) * (-((0 : ℝ) * q) / 2) * (-((0 : ℝ) * q) / 2) +
          Real.exp (-((0 : ℝ) ^ 2 * q) / 4) * (-q / 2) = -q / 2 - (0 : ℝ) ^ 2 := by simp
      rw [e] at h2
      exact h2.ofReal_comp
  · -- the characteristic function
    intro ξ
    rw [hχ ξ, hmean ξ]
    simp
