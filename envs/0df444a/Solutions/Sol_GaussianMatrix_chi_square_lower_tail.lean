-- Prove2me | solution 1 for GaussianMatrix.chi_square_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:03:59.719105+00:00
-- url     : https://prove2.me/submissions/6ff8fc1a-090c-44d2-b327-03b50ab63da8

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- For `s ≥ 0`, `E[exp(-s X²)] = (1 + 2 s)^{-1/2}` for a standard Gaussian `X`. -/
lemma integral_exp_neg_mul_sq_gaussianReal {s : ℝ} (hs : 0 ≤ s) :
    ∫ x, Real.exp (-s * x ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 + 2 * s))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal, smul_eq_mul, sub_zero, NNReal.coe_one, mul_one]
  have h : ∀ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-s * x ^ 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 + s) * x ^ 2) := by
    intro x; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have h2 : Real.pi / (1 / 2 + s) = (2 * Real.pi) / (1 + 2 * s) := by
    field_simp
  rw [h2, Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ 1 + 2 * s)]
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h1 : 0 < Real.sqrt (1 + 2 * s) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- Chernoff bound for the lower tail of a chi-square variable with `d` degrees of freedom. -/
lemma chi_square_chernoff {d : ℕ} (u s : ℝ) (hs : 0 ≤ s) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1).real {g | ∑ i, g i ^ 2 ≤ u}
      ≤ Real.exp (s * u) * ((Real.sqrt (1 + 2 * s))⁻¹) ^ d := by
  set μ := Measure.pi fun _ : Fin d => gaussianReal 0 1
  have hint : Integrable (fun g : Fin d → ℝ => Real.exp (-s * ∑ i, g i ^ 2)) μ := by
    refine Integrable.mono' (integrable_const (1:ℝ)) ?_ ?_
    · exact (by fun_prop : Measurable (fun g : Fin d → ℝ => Real.exp (-s * ∑ i, g i ^ 2))).aestronglyMeasurable
    · refine ae_of_all _ fun g => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith
  have h := measure_le_le_exp_mul_mgf (X := fun g : Fin d → ℝ => ∑ i, g i ^ 2) (μ := μ) u
    (neg_nonpos.mpr hs) hint
  have hmgf : mgf (fun g : Fin d → ℝ => ∑ i, g i ^ 2) μ (-s)
      = ((Real.sqrt (1 + 2 * s))⁻¹) ^ d := by
    simp only [mgf]
    have : ∀ g : Fin d → ℝ, Real.exp (-s * ∑ i, g i ^ 2) = ∏ i, Real.exp (-s * g i ^ 2) := by
      intro g; rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [this]
    rw [integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ x => Real.exp (-s * x ^ 2))]
    have h1 := integral_exp_neg_mul_sq_gaussianReal hs
    simp only [neg_mul] at h1
    simp [h1]
  rw [hmgf, neg_neg] at h
  exact h

end GaussianMatrix

open GaussianMatrix

theorem solution {d : ℕ} (hd : 1 ≤ d) (u : ℝ) (hu : 0 ≤ u) (hud : u ≤ d) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 1) {g | ∑ i, g i ^ 2 ≤ u}
      ≤ ENNReal.ofReal ((Real.exp 1 * u / d) ^ ((d : ℝ) / 2)) := by
  set μ := Measure.pi fun _ : Fin d => gaussianReal 0 1 with hμ
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  rcases hu.eq_or_lt with rfl | hu0
  · -- `u = 0`: the event forces `g = 0`, a null set.
    have hsub : {g : Fin d → ℝ | ∑ i, g i ^ 2 ≤ 0} ⊆ (fun g => g ⟨0, hd⟩) ⁻¹' {0} := by
      intro g hg
      simp only [Set.mem_ofPred_eq] at hg
      have h0 : ∀ i ∈ Finset.univ, g i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (g i))).mp
          (le_antisymm hg (Finset.sum_nonneg fun i _ => sq_nonneg _))
      simpa using h0 ⟨0, hd⟩ (Finset.mem_univ _)
    have hnull : μ ((fun g => g ⟨0, hd⟩) ⁻¹' {0}) = 0 := by
      rw [(measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) ⟨0, hd⟩).measure_preimage
        (measurableSet_singleton 0).nullMeasurableSet]
      have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      exact measure_singleton 0
    rw [measure_mono_null hsub hnull]
    exact zero_le
  · set s := ((d:ℝ) / u - 1) / 2 with hs_def
    have hdu : 1 ≤ (d:ℝ) / u := by rw [le_div_iff₀ hu0]; linarith
    have hs : 0 ≤ s := by rw [hs_def]; linarith
    have h1 : 1 + 2 * s = (d:ℝ) / u := by rw [hs_def]; ring
    have hsu : s * u = ((d:ℝ) - u) / 2 := by rw [hs_def]; field_simp
    have hch := chi_square_chernoff (d := d) u s hs
    rw [h1, hsu] at hch
    have hpow : ((Real.sqrt ((d:ℝ) / u))⁻¹) ^ d = (u / d) ^ ((d:ℝ) / 2) := by
      rw [← Real.sqrt_inv, inv_div, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
      congr 1; ring
    have hrhs : (Real.exp 1 * u / d) ^ ((d : ℝ) / 2)
        = Real.exp ((d:ℝ) / 2) * (u / d) ^ ((d:ℝ) / 2) := by
      rw [mul_div_assoc, Real.mul_rpow (Real.exp_pos 1).le (by positivity), Real.exp_one_rpow]
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    refine hch.trans ?_
    rw [hpow, hrhs]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact Real.exp_le_exp.mpr (by linarith)
