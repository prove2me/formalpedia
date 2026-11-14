-- Prove2me | solution 5 for BosonicLearn.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:55:37.116436+00:00
-- url     : https://prove2.me/submissions/cae48d46-a97c-40d6-aa9b-7902b8cfa760

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneSuccess
import Definitions.Def_BosonicLearn_promiseClass
import Theorems.Thm_BosonicLearn_eq_207
import Theorems.Thm_BosonicLearn_gaussian_sample_concentration
import Theorems.Thm_BosonicLearn_cov_perturbation_gap
import Theorems.Thm_BosonicLearn_lemma_18_classical
import Theorems.Thm_BosonicLearn_traceDist_triangle
import Theorems.Thm_BosonicLearn_loewner_trace_bound
import Theorems.Thm_BosonicLearn_loewner_inv_form_le
import Theorems.Thm_BosonicLearn_gaussianState_classical_family
import Theorems.Thm_BosonicLearn_gaussianState_exists_of_le

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

noncomputable section

/-! ### Numerical part of the proof -/

/-- With `t = χ/√N` small, the two error terms of the proof are at most `16ε/17` and `ε/17`.
The covariance term is measured against the constant `√2·(½+ν)/√(ν(1+ν))` of `cov_perturbation_gap`. -/
private lemma numerics (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) (ν ε χ : ℝ) (hν : 0 < ν) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hχ : 0 ≤ χ) (h : χ ^ 2 / N ≤ ε ^ 2 / (4624 * ((1 + 1 / ν) * n))) :
    0 ≤ 2 * χ / Real.sqrt N + 2 * χ ^ 2 / N ∧
    2 * χ / Real.sqrt N + 2 * χ ^ 2 / N ≤ 1 / 2 ∧
    (2 * (2 * χ / Real.sqrt N + 2 * χ ^ 2 / N) / (1 - (2 * χ / Real.sqrt N + 2 * χ ^ 2 / N)) *
        (1 + 1 / (1 + 2 * ν))) ^ 2 * (2 * n) ≤
      (16 / 17 * ε / (Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))))) ^ 2 ∧
    (1 + 1 / (1 + 2 * ν)) * (χ ^ 2 / N) ≤ 2 * (ε / 17) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  set t : ℝ := χ / Real.sqrt N with ht
  have ht0 : 0 ≤ t := div_nonneg hχ hsqrtN.le
  have ht2 : t ^ 2 = χ ^ 2 / N := by rw [ht, div_pow, Real.sq_sqrt hNpos.le]
  have hνi : 0 < 1 / ν := by positivity
  have hL1 : 1 ≤ 1 + 1 / ν := by linarith
  have hLn : 1 ≤ (1 + 1 / ν) * n := by nlinarith
  have hε2 : ε ^ 2 < 1 := by nlinarith
  have h1 : t ^ 2 ≤ ε ^ 2 / (4624 * ((1 + 1 / ν) * n)) := by rw [ht2]; exact h
  have h2 : ε ^ 2 / (4624 * ((1 + 1 / ν) * n)) ≤ ε ^ 2 / 4624 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith)
  have ht17 : t ≤ 1 / 17 := by
    have h3 : t ^ 2 ≤ (1 / 17) ^ 2 := by nlinarith [h1.trans h2]
    exact (pow_le_pow_iff_left₀ ht0 (by norm_num) two_ne_zero).mp h3
  have hζ : 2 * χ / Real.sqrt N + 2 * χ ^ 2 / N = 2 * t + 2 * t ^ 2 := by
    rw [ht2, ht]
    ring
  rw [hζ]
  have hζ0 : 0 ≤ 2 * t + 2 * t ^ 2 := by positivity
  have hζ4 : 2 * t + 2 * t ^ 2 ≤ 4 * t := by nlinarith
  have hζhalf : 2 * t + 2 * t ^ 2 ≤ 1 / 2 := by nlinarith
  have hα2 : 1 + 1 / (1 + 2 * ν) ≤ 2 := by
    have h3 : 1 / (1 + 2 * ν) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hα0 : 0 < 1 + 1 / (1 + 2 * ν) := by positivity
  refine ⟨hζ0, hζhalf, ?_, ?_⟩
  · have h1ζ : 0 < 1 - (2 * t + 2 * t ^ 2) := by linarith
    have h3 : 2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) ≤ 4 * (2 * t + 2 * t ^ 2) := by
      rw [div_le_iff₀ h1ζ]
      nlinarith
    have h30 : 0 ≤ 2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) := by positivity
    have hc : 2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) * (1 + 1 / (1 + 2 * ν)) ≤ 32 * t := by
      calc 2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) * (1 + 1 / (1 + 2 * ν))
          ≤ 4 * (2 * t + 2 * t ^ 2) * 2 := mul_le_mul h3 hα2 hα0.le (by positivity)
        _ ≤ 32 * t := by linarith
    have hc0 : 0 ≤ 2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) * (1 + 1 / (1 + 2 * ν)) :=
      mul_nonneg h30 hα0.le
    have hc2 := pow_le_pow_left₀ hc0 hc 2
    have hν1 : 0 < ν * (1 + ν) := by positivity
    have hR : (16 / 17 * ε / (Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))))) ^ 2 =
        512 / 289 * ε ^ 2 * (ν * (1 + ν) / (1 + 2 * ν) ^ 2) := by
      have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs : Real.sqrt (ν * (1 + ν)) ^ 2 = ν * (1 + ν) := Real.sq_sqrt hν1.le
      have e : (Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν)))) ^ 2 =
          2 * (1 / 2 + ν) ^ 2 / (ν * (1 + ν)) := by
        rw [mul_pow, div_pow, hs2, hs]
        ring
      rw [div_pow, e]
      field_simp
      ring
    rw [hR]
    have hLγ : 1 / (1 + 1 / ν) ≤ 4 * (ν * (1 + ν) / (1 + 2 * ν) ^ 2) := by
      have h4 : 1 / (1 + 1 / ν) = ν / (1 + ν) := by
        field_simp
        ring
      have h5 : 4 * (ν * (1 + ν)) * (1 + ν) - ν * (1 + 2 * ν) ^ 2 = ν * (3 + 4 * ν) := by ring
      have h6 : 0 ≤ ν * (3 + 4 * ν) := by positivity
      rw [h4, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hn0 : (0 : ℝ) < n := by linarith
    calc (2 * (2 * t + 2 * t ^ 2) / (1 - (2 * t + 2 * t ^ 2)) * (1 + 1 / (1 + 2 * ν))) ^ 2 * (2 * n)
        ≤ (32 * t) ^ 2 * (2 * n) := mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ = 2048 * n * t ^ 2 := by ring
      _ ≤ 2048 * n * (ε ^ 2 / (4624 * ((1 + 1 / ν) * n))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 128 / 289 * ε ^ 2 * (1 / (1 + 1 / ν)) := by
          field_simp
          ring
      _ ≤ 128 / 289 * ε ^ 2 * (4 * (ν * (1 + ν) / (1 + 2 * ν) ^ 2)) :=
          mul_le_mul_of_nonneg_left hLγ (by positivity)
      _ = 512 / 289 * ε ^ 2 * (ν * (1 + ν) / (1 + 2 * ν) ^ 2) := by ring
  · have h3 : (1 + 1 / (1 + 2 * ν)) * (χ ^ 2 / N) ≤ 2 * t ^ 2 := by
      rw [← ht2]
      exact mul_le_mul_of_nonneg_right hα2 (by positivity)
    have h4 : 2 * (ε / 17) ^ 2 = 2 * ε ^ 2 / 289 := by ring
    rw [h4]
    have h5 := h1.trans h2
    nlinarith [sq_nonneg ε]

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

private lemma det_bound {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (ν ε δ : ℝ) (hν : 0 < ν) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hχ : chi n δ ^ 2 / N ≤ ε ^ 2 / (4624 * ((1 + 1 / ν) * n)))
    (gs : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) → State (Occupation (Fin n)))
    (hgs : ∀ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
      (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef →
      IsGaussianState (gs (μ, fun a b => S a b)) μ S)
    (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hρ : IsGaussianState ρ μ S)
    (hS : (S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (Y : Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n))
    (hY1 : (muHat Y - μ) ⬝ᵥ ((S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))⁻¹ *ᵥ
      (muHat Y - μ)) ≤ chi n δ ^ 2 / N)
    (hY2 : (cHat Y - (1 - zeta n N δ) •
      (S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))).PosSemidef)
    (hY3 : ((1 + zeta n N δ) •
      (S + (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) - cHat Y).PosSemidef) :
    traceDist (gs (muHat Y, fun a b => sigTilde δ Y a b)).coefficients ρ.coefficients ≤
      ENNReal.ofReal ε := by
  obtain ⟨hζ0, hζ1, hT, hq⟩ := numerics n N hn hN ν ε (chi n δ) hν hε0 hε1 (chi_nonneg n δ) hχ
  have hζdef : zeta n N δ = 2 * chi n δ / Real.sqrt N + 2 * chi n δ ^ 2 / N := rfl
  rw [← hζdef] at hζ0 hζ1 hT
  set ζ : ℝ := zeta n N δ with hζ
  set C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := S + (1 / 2 : ℝ) • 1 with hC
  set α : ℝ := 1 + 1 / (1 + 2 * ν) with hα
  set St : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := sigTilde δ Y with hSt
  have h1ζ : 0 < 1 - ζ := by linarith
  have h1ζ' : 1 - ζ ≠ 0 := h1ζ.ne'
  have hν' : 1 + 2 * ν ≠ 0 := by positivity
  have hαpos : 0 < α := by positivity
  -- `D = Σ̃ − Σ` is a non-negative multiple of `Ĉ − (1 − ζ) C`
  have hD_eq : St - S = (1 / (1 - ζ)) • (cHat Y - (1 - ζ) • C) := by
    ext a b
    simp only [hSt, sigTilde, hC, ← hζ, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    field_simp
    ring
  have hD : (St - S).PosSemidef := by
    rw [hD_eq]
    exact hY2.smul (by positivity)
  -- `C ⪯ α Σ`
  have hαSC : (α • S - C).PosSemidef := by
    have e : α • S - C = (1 / (1 + 2 * ν)) • (S - (1 / 2 + ν) • 1) := by
      ext a b
      simp only [hα, hC, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [e]
    exact hS.smul (by positivity)
  -- `D ⪯ c Σ` with `c = 2ζ/(1 − ζ) · α`
  have hc0 : 0 ≤ 2 * ζ / (1 - ζ) * α := by positivity
  have hcD : ((2 * ζ / (1 - ζ) * α) • S - (St - S)).PosSemidef := by
    have e : (2 * ζ / (1 - ζ) * α) • S - (St - S) =
        (2 * ζ / (1 - ζ)) • (α • S - C) + (1 / (1 - ζ)) • ((1 + ζ) • C - cHat Y) := by
      rw [hD_eq]
      ext a b
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [e]
    exact (hαSC.smul (by positivity)).add (hY3.smul (by positivity))
  -- positive definiteness of `Σ` and `C`
  have hSpd : S.PosDef := by
    have e : S = (S - (1 / 2 + ν) • 1) + (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
      rw [sub_add_cancel]
    rw [e]
    exact Matrix.PosDef.posSemidef_add hS (Matrix.PosDef.one.smul (by positivity))
  have hCpd : C.PosDef := hSpd.add_posSemidef (Matrix.PosSemidef.one.smul (by norm_num))
  -- the states
  have hSthalf : (St - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef := by
    have e : St - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        (St - S) + (S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) +
          ν • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
      rw [add_smul]; abel
    rw [e]
    exact (hD.add hS).add (Matrix.PosSemidef.one.smul hν.le)
  have hest : IsGaussianState (gs (muHat Y, fun a b => St a b)) (muHat Y) St := hgs _ _ hSthalf
  have hzero : (S - S).PosSemidef := by
    rw [sub_self]
    exact Matrix.PosSemidef.zero
  obtain ⟨ρm, hρm⟩ := gaussianState_exists_of_le ρ μ S hρ (muHat Y) S hzero
  -- the two error terms: covariance (common mean `μ̂`) and mean (common covariance `Σ`)
  have hgap := cov_perturbation_gap ρm (gs (muHat Y, fun a b => St a b)) (muHat Y) S St ν hν hS hD
    hρm hest
  have hShalf : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef := by
    have e : S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        (S - (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) +
          ν • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
      rw [add_smul]; abel
    rw [e]
    exact hS.add (Matrix.PosSemidef.one.smul hν.le)
  have h18 := lemma_18_classical ρ ρm μ (muHat Y) S hShalf hρ hρm
  have htri := traceDist_triangle (gs (muHat Y, fun a b => St a b)).coefficients ρm.coefficients
    ρ.coefficients
  have hT' := loewner_trace_bound S (St - S) hSpd hD (2 * ζ / (1 - ζ) * α) hc0 hcD
  have hcard : (Fintype.card (Fin n ⊕ Fin n) : ℝ) = 2 * n := by
    simp
    ring
  rw [hcard] at hT'
  have hq' := loewner_inv_form_le C S hCpd hSpd α hαpos hαSC (muHat Y - μ)
  have hcA : 0 < Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))) := by positivity
  have he1 : Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))) *
      Real.sqrt (S⁻¹ * (St - S) * S⁻¹ * (St - S)).trace ≤ 16 / 17 * ε := by
    have hsq : Real.sqrt (S⁻¹ * (St - S) * S⁻¹ * (St - S)).trace ≤
        16 / 17 * ε / (Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν)))) :=
      Real.sqrt_le_iff.mpr ⟨by positivity, hT'.trans hT⟩
    rw [le_div_iff₀ hcA] at hsq
    linarith
  have he2 : Real.sqrt ((muHat Y - μ) ⬝ᵥ (S⁻¹ *ᵥ (muHat Y - μ))) / Real.sqrt 2 ≤ ε / 17 := by
    have hq2 : ((muHat Y - μ) ⬝ᵥ (S⁻¹ *ᵥ (muHat Y - μ))) ≤ 2 * (ε / 17) ^ 2 :=
      hq'.trans ((mul_le_mul_of_nonneg_left hY1 hαpos.le).trans hq)
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    calc Real.sqrt ((muHat Y - μ) ⬝ᵥ (S⁻¹ *ᵥ (muHat Y - μ))) ≤ Real.sqrt (2 * (ε / 17) ^ 2) := Real.sqrt_le_sqrt hq2
      _ = Real.sqrt 2 * (ε / 17) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
      _ = ε / 17 * Real.sqrt 2 := by ring
  calc traceDist (gs (muHat Y, fun a b => St a b)).coefficients ρ.coefficients
      ≤ traceDist (gs (muHat Y, fun a b => St a b)).coefficients ρm.coefficients +
          traceDist ρm.coefficients ρ.coefficients := htri
    _ ≤ ENNReal.ofReal (Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))) *
          Real.sqrt (S⁻¹ * (St - S) * S⁻¹ * (St - S)).trace) +
        ENNReal.ofReal (Real.sqrt ((muHat Y - μ) ⬝ᵥ (S⁻¹ *ᵥ (muHat Y - μ))) / Real.sqrt 2) :=
        add_le_add hgap h18
    _ = ENNReal.ofReal (Real.sqrt 2 * ((1 / 2 + ν) / Real.sqrt (ν * (1 + ν))) *
          Real.sqrt (S⁻¹ * (St - S) * S⁻¹ * (St - S)).trace +
        Real.sqrt ((muHat Y - μ) ⬝ᵥ (S⁻¹ *ᵥ (muHat Y - μ))) / Real.sqrt 2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
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

private lemma success_bound {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (ν ε δ : ℝ) (hν : 0 < ν) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hχ : chi n δ ^ 2 / N ≤ ε ^ 2 / (4624 * ((1 + 1 / ν) * n)))
    (gs : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) → State (Occupation (Fin n)))
    (hgs : ∀ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
      (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef →
      IsGaussianState (gs (μ, fun a b => S a b)) μ S)
    (ρ : State (Occupation (Fin n))) (hρ : ρ ∈ promiseClass n ν) :
    ENNReal.ofReal (1 - δ) ≤
      heterodyneSuccess N (fun Y => gs (muHat Y, fun a b => sigTilde δ Y a b)) ρ ε := by
  obtain ⟨μ, S, hG, hS⟩ := hρ
  have hSpd : S.PosDef := by
    have e : S = (S - (1 / 2 + ν) • 1) + (1 / 2 + ν) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
      rw [sub_add_cancel]
    rw [e]
    exact Matrix.PosDef.posSemidef_add hS (Matrix.PosDef.one.smul (by positivity))
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
    det_bound hn hN ν ε δ hν hε0 hε1 hχ gs hgs ρ μ S hG hS Y hY.1 hY.2.1 hY.2.2)

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
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ν : ℝ), 0 < ν → ∀ ϵ δ : ℝ, 0 < ϵ → ϵ < 1 → 0 < δ → δ < 1 →
      ∃ N : ℕ, (N : ℝ) ≤ C * ((1 + 1 / ν) * ((n : ℝ) * (n + Real.log (1 / δ))) / ϵ ^ 2) ∧
        ∃ est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)),
          Measurable est ∧
          (∀ y, ∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
            IsGaussianState (est y) μ S) ∧
          ∀ ρ ∈ promiseClass n ν, ENNReal.ofReal (1 - δ) ≤ heterodyneSuccess N est ρ ϵ := by
  refine ⟨55489, by norm_num, fun n ν hν ε δ hε0 hε1 hδ0 hδ1 => ?_⟩
  obtain ⟨gs, hgsm, hgsG, hgs⟩ := gaussianState_classical_family n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, by simp, fun _ => gs (0, 0), measurable_const, fun y => hgsG _, fun ρ _ => ?_⟩
    unfold heterodyneSuccess
    have hset : {y : Fin 0 → EuclideanSpace ℝ (Fin 0 ⊕ Fin 0) |
        traceDist (gs (0, 0)).coefficients ρ.coefficients ≤ ENNReal.ofReal ε} = Set.univ := by
      ext y
      simp [traceDist_zero_modes ρ (gs (0, 0))]
    rw [hset, Measure.pi_of_empty, measure_univ]
    exact ENNReal.ofReal_le_one.mpr (by linarith)
  · have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by
      rw [le_div_iff₀ hδ0]
      linarith)
    have hνi : 0 < 1 / ν := by positivity
    have hm1 : 1 ≤ (n : ℝ) + Real.log (1 / δ) := by linarith
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith
    have hε2pos : 0 < ε ^ 2 := by positivity
    have hεB : ε ^ 2 * ((1 + 1 / ν) * ((n : ℝ) * (n + Real.log (1 / δ))) / ε ^ 2) =
        (1 + 1 / ν) * ((n : ℝ) * (n + Real.log (1 / δ))) := by
      field_simp
    have hLnm : 1 ≤ (1 + 1 / ν) * ((n : ℝ) * (n + Real.log (1 / δ))) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le hnr hm1)
    have hB1 : 1 ≤ (1 + 1 / ν) * ((n : ℝ) * (n + Real.log (1 / δ))) / ε ^ 2 := by
      rw [le_div_iff₀ hε2pos]
      linarith
    set B : ℝ := (1 + 1 / ν) * ((n : ℝ) * (n + Real.log (1 / δ))) / ε ^ 2 with hB
    have hNge : 55488 * B ≤ (⌈55488 * B⌉₊ : ℝ) := Nat.le_ceil _
    have hNlt : (⌈55488 * B⌉₊ : ℝ) < 55488 * B + 1 := Nat.ceil_lt_add_one (by positivity)
    have hN1 : 1 ≤ ⌈55488 * B⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
    have hχ : chi n δ ^ 2 / (⌈55488 * B⌉₊ : ℝ) ≤ ε ^ 2 / (4624 * ((1 + 1 / ν) * n)) := by
      have h8 := chi_sq_le n hn δ hδ0 hδ1
      have hNpos : (0 : ℝ) < ⌈55488 * B⌉₊ := by exact_mod_cast hN1
      rw [div_le_div_iff₀ hNpos (by positivity)]
      have hLn : 0 ≤ 4624 * ((1 + 1 / ν) * (n : ℝ)) := by positivity
      calc chi n δ ^ 2 * (4624 * ((1 + 1 / ν) * n))
          ≤ 12 * ((n : ℝ) + Real.log (1 / δ)) * (4624 * ((1 + 1 / ν) * n)) :=
            mul_le_mul_of_nonneg_right h8 hLn
        _ = 55488 * (ε ^ 2 * B) := by
            rw [hεB]
            ring
        _ = ε ^ 2 * (55488 * B) := by ring
        _ ≤ ε ^ 2 * (⌈55488 * B⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hNge hε2pos.le
    refine ⟨⌈55488 * B⌉₊, by linarith, fun Y => gs (muHat Y, fun a b => sigTilde δ Y a b),
      est_measurable δ gs hgsm, fun y => hgsG _, fun ρ hρ =>
        success_bound hn hN1 ν ε δ hν hε0 hε1 hδ0 hδ1 hχ gs hgs ρ hρ⟩
