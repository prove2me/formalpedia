-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_predictable_finite_measure_gaussian_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:45:28.365363+00:00
-- url     : https://prove2.me/submissions/77ce80d5-b783-40e9-9e80-b489adeb0656

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_source_interior_compact_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded original discounted Gaussian derivative coefficient has finite
    square energy on any finite predictable measure, with no change of sigma algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (U : ℝ≥0 × Ω → ℝ) (hU : ∀ p, U p ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ p : ℝ≥0 × Ω,
        |Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))| ≤ K) ∧
      (∫⁻ p, ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))) ^ 2) ∂μ) < ⊤ := by
  obtain ⟨B, hB⟩ := avram_p4_f3_source_interior_compact_derivative_bound
    w C hw (avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen C) a b hband
  let K : ℝ := |X.σ| * max B 0
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg _) (le_max_right B 0)
  have hcoef (p : ℝ≥0 × Ω) :
      |Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))| ≤ K := by
    have hexp : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have ht : 0 ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
      nlinarith [mul_nonneg hq ht]
    calc
      _ = Real.exp (-(q * (p.1 : ℝ))) * (|X.σ| * |deriv w (U p)|) := by
        rw [abs_mul, abs_mul, Real.abs_exp]
      _ ≤ Real.exp (-(q * (p.1 : ℝ))) * (|X.σ| * max B 0) := by
        gcongr
        exact (hB (U p) (hU p)).trans (le_max_left B 0)
      _ ≤ 1 * (|X.σ| * max B 0) := by gcongr
      _ = K := by simp [K]
  have hcoefSq (p : ℝ≥0 × Ω) :
      (Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))) ^ 2 ≤ K ^ 2 := by
    let z : ℝ := Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))
    have hz : |z| ≤ K := hcoef p
    have hmult : 0 ≤ (K - |z|) * (K + |z|) :=
      mul_nonneg (sub_nonneg.mpr hz) (add_nonneg hK (abs_nonneg z))
    have hsabs : |z| ^ 2 = z ^ 2 := by rw [sq_abs]
    change z ^ 2 ≤ K ^ 2
    nlinarith [hmult, hsabs]
  refine ⟨K, hK, hcoef, ?_⟩
  calc
    _ ≤ ENNReal.ofReal (K ^ 2) * μ Set.univ := by
      calc
        _ ≤ ∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal (K ^ 2) ∂μ :=
          lintegral_mono (fun p => ENNReal.ofReal_le_ofReal (hcoefSq p))
        _ = ENNReal.ofReal (K ^ 2) * μ Set.univ := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ
