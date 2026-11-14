-- Prove2me | solution 1 for BosonicLearn.bmem25_theorem_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T18:32:25.004851+00:00
-- url     : https://prove2.me/submissions/da6d0580-789b-47ec-9832-d93ec7c5d692
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneSuccess
import Definitions.Def_BosonicLearn_IsGaussianState
import Theorems.Thm_BosonicLearn_eq_207
import Theorems.Thm_BosonicLearn_gaussian_sample_concentration
import Theorems.Thm_BosonicLearn_lemma_18
import Theorems.Thm_BosonicLearn_traceDist_triangle
import Theorems.Thm_BosonicLearn_traceDist_le_one
import Theorems.Thm_BosonicLearn_loewner_inv_form_le
import Theorems.Thm_BosonicLearn_gaussianState_measurable_family
import Theorems.Thm_BosonicLearn_gaussianState_exists_of_le
import Theorems.Thm_BosonicLearn_bmem25_theorem_8_cov

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

noncomputable section

/-! ### Numerical part of the proof -/

private lemma numerics2 (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) (ε χ : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hχ : 0 ≤ χ) (h : χ ^ 2 / N ≤ ε ^ 2 / (3600 * (n : ℝ) ^ 2)) :
    0 ≤ 2 * χ / Real.sqrt N + 2 * χ ^ 2 / N ∧
    2 * χ / Real.sqrt N + 2 * χ ^ 2 / N ≤ 1 / 2 ∧
    (1 + Real.sqrt 3) / 8 * (2 * ((2 * (2 * χ / Real.sqrt N + 2 * χ ^ 2 / N) /
        (1 - (2 * χ / Real.sqrt N + 2 * χ ^ 2 / N)) * 2) * (2 * n))) ≤ 4 / 5 * ε ∧
    2 * (χ ^ 2 / N) ≤ (2 * ε / 5) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  set t : ℝ := χ / Real.sqrt N with ht
  have ht0 : 0 ≤ t := div_nonneg hχ hsqrtN.le
  have ht2 : t ^ 2 = χ ^ 2 / N := by rw [ht, div_pow, Real.sq_sqrt hNpos.le]
  have h1 : t ^ 2 ≤ (ε / (60 * n)) ^ 2 := by
    rw [ht2, div_pow, mul_pow]
    norm_num
    exact h
  have ht60 : t ≤ ε / (60 * n) :=
    (pow_le_pow_iff_left₀ ht0 (by positivity) two_ne_zero).mp h1
  have hnt : n * t ≤ ε / 60 := by
    have h2 := mul_le_mul_of_nonneg_left ht60 hn0.le
    calc n * t ≤ n * (ε / (60 * n)) := h2
      _ = ε / 60 := by field_simp
  have ht1 : t ≤ 1 / 60 := by nlinarith
  have hζ : 2 * χ / Real.sqrt N + 2 * χ ^ 2 / N = 2 * t + 2 * t ^ 2 := by
    rw [ht2, ht]
    ring
  rw [hζ]
  have hζ0 : 0 ≤ 2 * t + 2 * t ^ 2 := by positivity
  have hζ4 : 2 * t + 2 * t ^ 2 ≤ 4 * t := by nlinarith
  have hζhalf : 2 * t + 2 * t ^ 2 ≤ 1 / 2 := by nlinarith
  refine ⟨hζ0, hζhalf, ?_, ?_⟩
  · have h1ζ : 0 < 1 - (2 * t + 2 * t ^ 2) := by linarith
    have h3 : 2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) ≤ 4 * (2 * t + 2 * t ^ 2) := by
      rw [div_le_iff₀ h1ζ]
      nlinarith
    have h30 : 0 ≤ 2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) := by positivity
    have hc : 2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) * 2 ≤ 32 * t := by nlinarith
    have hc0 : 0 ≤ 2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) * 2 := by positivity
    have hs3 : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hk : (1 + Real.sqrt 3) / 8 ≤ 3 / 8 := by linarith
    have hk0 : 0 ≤ (1 + Real.sqrt 3) / 8 := by positivity
    have hin : 2 * ((2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) * 2) * (2 * n)) ≤
        2 * ((32 * t) * (2 * n)) := by
      have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 2 * n)
      linarith
    have hin0 : 0 ≤ 2 * ((32 * t) * (2 * (n : ℝ))) := by positivity
    calc (1 + Real.sqrt 3) / 8 *
          (2 * ((2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) * 2) * (2 * n)))
        ≤ (1 + Real.sqrt 3) / 8 * (2 * ((32 * t) * (2 * n))) := mul_le_mul_of_nonneg_left hin hk0
      _ ≤ 3 / 8 * (2 * ((32 * t) * (2 * n))) := mul_le_mul_of_nonneg_right hk hin0
      _ = 48 * (n * t) := by ring
      _ ≤ 48 * (ε / 60) := mul_le_mul_of_nonneg_left hnt (by norm_num)
      _ = 4 / 5 * ε := by ring
  · have h4 : (2 * ε / 5) ^ 2 = 4 * ε ^ 2 / 25 := by ring
    rw [h4, ← ht2]
    have h5 : t ^ 2 ≤ ε ^ 2 / 3600 := by
      have h6 : (ε / (60 * n)) ^ 2 ≤ ε ^ 2 / 3600 := by
        rw [div_pow, mul_pow]
        norm_num
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
        nlinarith
      exact h1.trans h6
    nlinarith [sq_nonneg ε]

open scoped MatrixOrder in
/-- The trace of a product of two positive semidefinite matrices is non-negative. -/
private lemma trace_mul_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {P Q : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  have h := (hP.mul_mul_conjTranspose_same B).trace_nonneg
  have e : (P * (star B * B)).trace = (B * P * Bᴴ).trace := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [e]
  exact h

/-! ### The estimator -/

private def chi (n : ℕ) (δ : ℝ) : ℝ := Real.sqrt (2 * n) + Real.sqrt (2 * Real.log (3 / δ))

private def zeta (n N : ℕ) (δ : ℝ) : ℝ := 2 * chi n δ / Real.sqrt N + 2 * chi n δ ^ 2 / N

private lemma chi_nonneg (n : ℕ) (δ : ℝ) : 0 ≤ chi n δ :=
  add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Empirical mean of the heterodyne outcomes. -/
private def muHat {n N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) : Fin n ⊕ Fin n → ℝ :=
  fun a => (1 / (N : ℝ)) * ∑ j, WithLp.ofLp (Y j) a

/-- Centered empirical covariance of the heterodyne outcomes. -/
private def cHat {n N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.of fun a b => (1 / (N : ℝ)) * ∑ j,
    (WithLp.ofLp (Y j) a - muHat Y a) * (WithLp.ofLp (Y j) b - muHat Y b)

/-- The covariance estimate `Σ̃ = Ĉ/(1 − ζ) − ½I`. -/
private def sigTilde {n N : ℕ} (δ : ℝ) (Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  (1 / (1 - zeta n N δ)) • cHat Y - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)

/-! ### The error on the good event -/

private lemma det_bound2 {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (ε δ : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hχ : chi n δ ^ 2 / N ≤ ε ^ 2 / (3600 * (n : ℝ) ^ 2))
    (gs : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) → State (Occupation (Fin n)))
    (hgs : ∀ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
      (ρ : State (Occupation (Fin n))), IsGaussianState ρ μ S →
      IsGaussianState (gs (μ, fun a b => S a b)) μ S)
    (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hρ : IsGaussianState ρ μ S)
    (hS : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosDef)
    (Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n))
    (hY1 : (muHat Y - μ) ⬝ᵥ ((S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))⁻¹ *ᵥ
      (muHat Y - μ)) ≤ chi n δ ^ 2 / N)
    (hY2 : (cHat Y - (1 - zeta n N δ) •
      (S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))).PosSemidef)
    (hY3 : ((1 + zeta n N δ) •
      (S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) - cHat Y).PosSemidef) :
    traceDist (gs (muHat Y, fun a b => sigTilde δ Y a b)).coefficients ρ.coefficients ≤
      ENNReal.ofReal ε := by
  obtain ⟨hζ0, hζ1, hT, hq⟩ := numerics2 n N hn hN ε (chi n δ) hε0 hε1 (chi_nonneg n δ) hχ
  have hζdef : zeta n N δ = 2 * chi n δ / Real.sqrt N + 2 * chi n δ ^ 2 / N := rfl
  rw [← hζdef] at hζ0 hζ1 hT
  set ζ : ℝ := zeta n N δ with hζ
  set C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := S + (1 / 2 : ℝ) • 1 with hC
  set St : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := sigTilde δ Y with hSt
  have h1ζ : 0 < 1 - ζ := by linarith
  have h1ζ' : 1 - ζ ≠ 0 := h1ζ.ne'
  have hD_eq : St - S = (1 / (1 - ζ)) • (cHat Y - (1 - ζ) • C) := by
    ext a b
    simp only [hSt, sigTilde, hC, ← hζ, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    field_simp
    ring
  have hD : (St - S).PosSemidef := by
    rw [hD_eq]
    exact hY2.smul (by positivity)
  -- `C ⪯ 2 Σ`
  have hαSC : ((2 : ℝ) • S - C).PosSemidef := by
    have e : (2 : ℝ) • S - C = S - (1 / 2 : ℝ) • 1 := by
      ext a b
      simp only [hC, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact hS.posSemidef
  have hc0 : 0 ≤ 2 * ζ / (1 - ζ) * 2 := by positivity
  have hcD : ((2 * ζ / (1 - ζ) * 2) • S - (St - S)).PosSemidef := by
    have e : (2 * ζ / (1 - ζ) * 2) • S - (St - S) =
        (2 * ζ / (1 - ζ)) • ((2 : ℝ) • S - C) + (1 / (1 - ζ)) • ((1 + ζ) • C - cHat Y) := by
      rw [hD_eq]
      ext a b
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [e]
    exact (hαSC.smul (by positivity)).add (hY3.smul (by positivity))
  have hSpd : S.PosDef := by
    have e : S = (S - (1 / 2 : ℝ) • 1) + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
      rw [sub_add_cancel]
    rw [e]
    exact hS.add_posSemidef (Matrix.PosSemidef.one.smul (by norm_num))
  have hCpd : C.PosDef := hSpd.add_posSemidef (Matrix.PosSemidef.one.smul (by norm_num))
  have hStpd : St.PosDef := by
    have e : St = S + (St - S) := by rw [add_sub_cancel]
    rw [e]
    exact hSpd.add_posSemidef hD
  -- the states
  obtain ⟨ρt, hρt⟩ := gaussianState_exists_of_le ρ μ S hρ (muHat Y) St hD
  have hest : IsGaussianState (gs (muHat Y, fun a b => St a b)) (muHat Y) St := hgs _ _ ρt hρt
  have hzero : (S - S).PosSemidef := by
    rw [sub_self]
    exact Matrix.PosSemidef.zero
  obtain ⟨ρm, hρm⟩ := gaussianState_exists_of_le ρ μ S hρ (muHat Y) S hzero
  have hbm := bmem25_theorem_8_cov (gs (muHat Y, fun a b => St a b)) ρm (muHat Y) St S hest hρm hD
  have h18 := lemma_18 ρ ρm μ (muHat Y) S hρ hρm
  have htri := traceDist_triangle (gs (muHat Y, fun a b => St a b)).coefficients ρm.coefficients
    ρ.coefficients
  -- the trace term
  have hdetS : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSpd.isUnit
  have hcard : (Fintype.card (Fin n ⊕ Fin n) : ℝ) = 2 * n := by
    simp
    ring
  have htr1 : (S⁻¹ * (St - S)).trace ≤ (2 * ζ / (1 - ζ) * 2) * (2 * n) := by
    have h2 := trace_mul_nonneg hSpd.inv.posSemidef hcD
    have e2 : (S⁻¹ * ((2 * ζ / (1 - ζ) * 2) • S - (St - S))).trace =
        (2 * ζ / (1 - ζ) * 2) * Fintype.card (Fin n ⊕ Fin n) - (S⁻¹ * (St - S)).trace := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        Matrix.nonsing_inv_mul S hdetS, Matrix.trace_one]
    rw [e2, hcard] at h2
    linarith
  have hinvdiff : (S⁻¹ - St⁻¹).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (hSpd.isHermitian.inv.sub hStpd.isHermitian.inv) fun v => ?_
    have h1 : ((1 : ℝ) • St - S).PosSemidef := by
      rw [one_smul]
      exact hD
    have h2 := loewner_inv_form_le S St hSpd hStpd 1 one_pos h1 v
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith
  have htr2 : (St⁻¹ * (St - S)).trace ≤ (S⁻¹ * (St - S)).trace := by
    have h2 := trace_mul_nonneg hinvdiff hD
    rw [Matrix.sub_mul, Matrix.trace_sub] at h2
    linarith
  have htr : ((S⁻¹ + St⁻¹) * (St - S)).trace ≤ 2 * ((2 * ζ / (1 - ζ) * 2) * (2 * n)) := by
    rw [Matrix.add_mul, Matrix.trace_add]
    linarith
  have hk0 : 0 ≤ (1 + Real.sqrt 3) / 8 := by positivity
  have he1 : (1 + Real.sqrt 3) / 8 * ((S⁻¹ + St⁻¹) * (St - S)).trace ≤ 4 / 5 * ε :=
    (mul_le_mul_of_nonneg_left htr hk0).trans hT
  have hq' := loewner_inv_form_le C S hCpd hSpd 2 two_pos hαSC (muHat Y - μ)
  have he2 : 1 / 2 * Real.sqrt ((muHat Y - μ) ⬝ᵥ (S⁻¹ *ᵥ (muHat Y - μ))) ≤ ε / 5 := by
    have hsq : Real.sqrt ((muHat Y - μ) ⬝ᵥ (S⁻¹ *ᵥ (muHat Y - μ))) ≤ 2 * ε / 5 :=
      Real.sqrt_le_iff.mpr ⟨by positivity,
        hq'.trans ((mul_le_mul_of_nonneg_left hY1 (by norm_num)).trans hq)⟩
    linarith
  have htrnn : 0 ≤ ((S⁻¹ + St⁻¹) * (St - S)).trace := by
    have h2 := trace_mul_nonneg (hSpd.inv.posSemidef.add hStpd.inv.posSemidef) hD
    exact h2
  calc traceDist (gs (muHat Y, fun a b => St a b)).coefficients ρ.coefficients
      ≤ traceDist (gs (muHat Y, fun a b => St a b)).coefficients ρm.coefficients +
          traceDist ρm.coefficients ρ.coefficients := htri
    _ ≤ ENNReal.ofReal ((1 + Real.sqrt 3) / 8 * ((S⁻¹ + St⁻¹) * (St - S)).trace) +
        ENNReal.ofReal (1 / 2 * Real.sqrt ((muHat Y - μ) ⬝ᵥ (S⁻¹ *ᵥ (muHat Y - μ)))) :=
        add_le_add hbm h18
    _ = ENNReal.ofReal ((1 + Real.sqrt 3) / 8 * ((S⁻¹ + St⁻¹) * (St - S)).trace +
        1 / 2 * Real.sqrt ((muHat Y - μ) ⬝ᵥ (S⁻¹ *ᵥ (muHat Y - μ)))) :=
        (ENNReal.ofReal_add (mul_nonneg hk0 htrnn) (by positivity)).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Measurability of the estimator -/

private lemma est_measurable {n N : ℕ} (δ : ℝ)
    (gs : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) → State (Occupation (Fin n)))
    (hgs : Measurable gs) :
    Measurable fun Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n) =>
      gs (muHat Y, fun a b => sigTilde δ Y a b) := by
  have hcoord : ∀ (j : Fin N) (a : Fin n ⊕ Fin n),
      Measurable fun Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n) => WithLp.ofLp (Y j) a :=
    fun j a => (measurable_pi_apply a).comp
      ((WithLp.measurable_ofLp 2 _).comp (measurable_pi_apply j))
  have hmu : ∀ a, Measurable fun Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n) => muHat Y a :=
    fun a => measurable_const.mul (Finset.measurable_sum _ fun j _ => hcoord j a)
  refine hgs.comp (Measurable.prodMk (measurable_pi_iff.mpr hmu) ?_)
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  have e : (fun Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n) => sigTilde δ Y a b) =
      fun Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n) => 1 / (1 - zeta n N δ) * ((1 / (N : ℝ)) * ∑ j,
        (WithLp.ofLp (Y j) a - muHat Y a) * (WithLp.ofLp (Y j) b - muHat Y b)) -
        (1 / 2 : ℝ) * (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) a b := by
    funext Y
    simp only [sigTilde, cHat, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [e]
  exact (measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun j _ =>
    ((hcoord j a).sub (hmu a)).mul ((hcoord j b).sub (hmu b))))).sub measurable_const

/-! ### The number of copies -/

private lemma chi_sq_le (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    chi n δ ^ 2 ≤ 12 * ((n : ℝ) + Real.log (1 / δ)) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ0]
    linarith)
  have hlog3 : Real.log (3 / δ) = Real.log 3 + Real.log (1 / δ) := by
    rw [show (3 : ℝ) / δ = 3 * (1 / δ) by ring, Real.log_mul (by norm_num) (by positivity)]
  have hl3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  have hl30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ 2 * Real.log (3 / δ) := by
    rw [hlog3]
    linarith
  unfold chi
  have ha := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * n by positivity)
  have hb := Real.sq_sqrt h2
  rw [hlog3] at hb
  rw [hlog3]
  nlinarith [sq_nonneg (Real.sqrt (2 * n) - Real.sqrt (2 * (Real.log 3 + Real.log (1 / δ))))]

/-! ### Success probability -/

private lemma success_bound2 {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (ε δ : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hχ : chi n δ ^ 2 / N ≤ ε ^ 2 / (3600 * (n : ℝ) ^ 2))
    (gs : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) → State (Occupation (Fin n)))
    (hgs : ∀ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
      (ρ : State (Occupation (Fin n))), IsGaussianState ρ μ S →
      IsGaussianState (gs (μ, fun a b => S a b)) μ S)
    (ρ : State (Occupation (Fin n)))
    (hρ : ∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
      IsGaussianState ρ μ S ∧
        (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosDef) :
    ENNReal.ofReal (1 - δ) ≤
      heterodyneSuccess N (fun Y => gs (muHat Y, fun a b => sigTilde δ Y a b)) ρ ε := by
  obtain ⟨μ, S, hG, hS⟩ := hρ
  have hSpd : S.PosDef := by
    have e : S = (S - (1 / 2 : ℝ) • 1) + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
      rw [sub_add_cancel]
    rw [e]
    exact hS.add_posSemidef (Matrix.PosSemidef.one.smul (by norm_num))
  have hCpd : (S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosDef :=
    hSpd.add_posSemidef (Matrix.PosSemidef.one.smul (by norm_num))
  have hlog3 : 0 < Real.log (3 / δ) := Real.log_pos (by
    rw [lt_div_iff₀ hδ0]
    linarith)
  have ht0 : 0 ≤ Real.sqrt (2 * Real.log (3 / δ)) := Real.sqrt_nonneg _
  have hexp : 3 * Real.exp (-Real.sqrt (2 * Real.log (3 / δ)) ^ 2 / 2) = δ := by
    rw [Real.sq_sqrt (by positivity), show -(2 * Real.log (3 / δ)) / 2 = -Real.log (3 / δ) by ring,
      Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hconc := gaussian_sample_concentration (n := n) N hN (Real.sqrt (2 * Real.log (3 / δ))) ht0 μ
    (S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) hCpd
  have h210 : ENNReal.ofReal (1 - δ) ≤
      (Measure.pi fun _ : Fin N => multivariateGaussian (WithLp.toLp 2 μ)
        (S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)))
        {Y | (muHat Y - μ) ⬝ᵥ
            ((S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))⁻¹ *ᵥ (muHat Y - μ)) ≤
              chi n δ ^ 2 / N ∧
          (cHat Y - (1 - zeta n N δ) •
            (S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))).PosSemidef ∧
          ((1 + zeta n N δ) •
            (S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) - cHat Y).PosSemidef} := by
    have h1 : ENNReal.ofReal (1 - δ) =
        1 - ENNReal.ofReal (3 * Real.exp (-Real.sqrt (2 * Real.log (3 / δ)) ^ 2 / 2)) := by
      rw [hexp, ENNReal.ofReal_sub 1 hδ0.le, ENNReal.ofReal_one]
    rw [h1]
    exact hconc
  unfold heterodyneSuccess
  rw [eq_207 ρ μ S hG]
  exact h210.trans (measure_mono fun Y hY =>
    det_bound2 hn hN ε δ hε0 hε1 hχ gs hgs ρ μ S hG hS Y hY.1 hY.2.1 hY.2.2)

/-! ### Zero modes -/

private lemma traceDist_zero_modes (ρ σ : State (Occupation (Fin 0))) :
    traceDist σ.coefficients ρ.coefficients = 0 := by
  have huniq : ∀ u v : Occupation (Fin 0), u = v := fun u v => funext fun i => i.elim0
  have hval : ∀ (τ : State (Occupation (Fin 0))) (u v : Occupation (Fin 0)),
      τ.coefficients u v = 1 := by
    intro τ u v
    have hd := τ.density
    rw [huniq v u]
    have him : (τ.coefficients u u).im = 0 := by
      classical
      have h := (hd.2.1 {u} (fun _ => 1)).1
      simpa using h
    have hre : (τ.coefficients u u).re = 1 := by
      have h := hd.2.2.2
      rw [tsum_eq_single u (fun i hi => absurd (huniq i u) hi)] at h
      exact h
    exact Complex.ext (by simp [hre]) (by simp [him])
  have heq : σ.coefficients - ρ.coefficients = 0 := by
    ext u v
    simp [hval σ u v, hval ρ u v]
  unfold traceDist
  rw [heq]
  have h0 : traceSize (0 : Matrix (Occupation (Fin 0)) (Occupation (Fin 0)) ℂ) = 0 := by
    refine le_antisymm ?_ (by simp)
    let e : NuclearExpansion (0 : Matrix (Occupation (Fin 0)) (Occupation (Fin 0)) ℂ) :=
      { left := fun _ => 0
        right := fun _ => 0
        summable := by simp [summable_zero]
        coefficients := by
          intro i j
          simp }
    have h : traceSize (0 : Matrix (Occupation (Fin 0)) (Occupation (Fin 0)) ℂ) ≤
        ENNReal.ofReal (∑' n : ℕ, ‖e.left n‖ * ‖e.right n‖) := iInf_le _ e
    simpa [e] using h
  rw [h0]
  simp

/-! ### The statement -/

theorem solution :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ϵ : ℝ), 0 < ϵ →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((n : ℝ) ^ 3 / ϵ ^ 2) ∧
        ∃ est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)),
          Measurable est ∧
          ∀ ρ : State (Occupation (Fin n)),
            (∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
              IsGaussianState ρ μ S ∧
                (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosDef) →
            ENNReal.ofReal (1 - δ) ≤ heterodyneSuccess N est ρ ϵ := by
  intro δ hδ0 hδ1
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ0]
    linarith)
  refine ⟨43200 * (1 + Real.log (1 / δ)) + 1, by positivity, fun n ε hε0 => ?_⟩
  obtain ⟨gs, hgsm, hgsG, hgs⟩ := gaussianState_measurable_family n
  have hC0 : 0 ≤ (43200 * (1 + Real.log (1 / δ)) + 1) * ((n : ℝ) ^ 3 / ε ^ 2) := by positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, by simpa using hC0, fun _ => gs (0, 0), measurable_const, fun ρ _ => ?_⟩
    unfold heterodyneSuccess
    have hset : {y : Fin 0 → EuclideanSpace ℝ (Fin 0 ⊕ Fin 0) |
        traceDist (gs (0, 0)).coefficients ρ.coefficients ≤ ENNReal.ofReal ε} = Set.univ := by
      ext y
      simp [traceDist_zero_modes ρ (gs (0, 0))]
    rw [hset, Measure.pi_of_empty, measure_univ]
    exact ENNReal.ofReal_le_one.mpr (by linarith)
  · by_cases hε1 : 1 ≤ ε
    · refine ⟨0, by simpa using hC0, fun _ => gs (0, 0), measurable_const, fun ρ _ => ?_⟩
      unfold heterodyneSuccess
      have hset : {y : Fin 0 → EuclideanSpace ℝ (Fin n ⊕ Fin n) |
          traceDist (gs (0, 0)).coefficients ρ.coefficients ≤ ENNReal.ofReal ε} = Set.univ := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact (traceDist_le_one _ _).trans (ENNReal.one_le_ofReal.mpr hε1)
      rw [hset, Measure.pi_of_empty, measure_univ]
      exact ENNReal.ofReal_le_one.mpr (by linarith)
    · rw [not_le] at hε1
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hε2pos : 0 < ε ^ 2 := by positivity
      have hm0 : 0 < (n : ℝ) + Real.log (1 / δ) := by linarith
      set B : ℝ := (n : ℝ) ^ 2 * ((n : ℝ) + Real.log (1 / δ)) / ε ^ 2 with hB
      have hB0 : 0 < B := by positivity
      have hNge : 43200 * B ≤ (⌈43200 * B⌉₊ : ℝ) := Nat.le_ceil _
      have hNlt : (⌈43200 * B⌉₊ : ℝ) < 43200 * B + 1 := Nat.ceil_lt_add_one (by positivity)
      have hN1 : 1 ≤ ⌈43200 * B⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
      have hεB : ε ^ 2 * B = (n : ℝ) ^ 2 * ((n : ℝ) + Real.log (1 / δ)) := by
        rw [hB]
        field_simp
      have hχ : chi n δ ^ 2 / (⌈43200 * B⌉₊ : ℝ) ≤ ε ^ 2 / (3600 * (n : ℝ) ^ 2) := by
        have h8 := chi_sq_le n hn δ hδ0 hδ1
        have hNpos : (0 : ℝ) < ⌈43200 * B⌉₊ := by exact_mod_cast hN1
        rw [div_le_div_iff₀ hNpos (by positivity)]
        calc chi n δ ^ 2 * (3600 * (n : ℝ) ^ 2)
            ≤ 12 * ((n : ℝ) + Real.log (1 / δ)) * (3600 * (n : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right h8 (by positivity)
          _ = 43200 * (ε ^ 2 * B) := by
              rw [hεB]
              ring
          _ = ε ^ 2 * (43200 * B) := by ring
          _ ≤ ε ^ 2 * (⌈43200 * B⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hNge hε2pos.le
      have hbound : (⌈43200 * B⌉₊ : ℝ) ≤
          (43200 * (1 + Real.log (1 / δ)) + 1) * ((n : ℝ) ^ 3 / ε ^ 2) := by
        have h1 : B ≤ (1 + Real.log (1 / δ)) * ((n : ℝ) ^ 3 / ε ^ 2) := by
          rw [hB, ← mul_div_assoc, div_le_div_iff_of_pos_right hε2pos]
          nlinarith [mul_nonneg hlog (sq_nonneg (n : ℝ)), mul_nonneg hlog
            (mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hnr))]
        have h2 : 1 ≤ (n : ℝ) ^ 3 / ε ^ 2 := by
          rw [le_div_iff₀ hε2pos]
          have h3 : ε ^ 2 ≤ 1 := by nlinarith
          have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnr
          linarith
        nlinarith
      refine ⟨⌈43200 * B⌉₊, hbound, fun Y => gs (muHat Y, fun a b => sigTilde δ Y a b),
        est_measurable δ gs hgsm, fun ρ hρ =>
          success_bound2 hn hN1 ε δ hε0 hε1 hδ0 hδ1 hχ gs hgs ρ hρ⟩
