-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:34:13.04269+00:00
-- url     : https://prove2.me/submissions/5cd49bce-c0b0-404f-abb0-3a48a6aa5773

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_finite_mesh_discount_error
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_exact_discount_nnreal_width_oscillation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original discounted mesh cash has error at most q times width times full mesh mass. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 ≤ h)
    (s : Finset ι) (a b : ι → ℝ≥0)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hmesh : ∀ i ∈ s, (b i : ℝ) - (a i : ℝ) ≤ h) :
    (∑ i ∈ s, ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
      dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) ≤
    (∑ i ∈ s, ∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ∧
    (∑ i ∈ s, ∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ≤
      (∑ i ∈ s, ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
        dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) +
      ENNReal.ofReal (q * h) *
        (∑ i ∈ s, dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by
  have hdelta : ∀ i ∈ s,
      ENNReal.ofReal (Real.exp (-(q * (a i : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) + ENNReal.ofReal (q * h) := by
    intro i hi
    have habR : (a i : ℝ) ≤ (b i : ℝ) := by exact_mod_cast hab i hi
    have hwidth := mul_le_mul_of_nonneg_left (hmesh i hi) hq
    have hpoint :=
      avram_p4_d_dividend_original_exact_discount_nnreal_width_oscillation
        q (a i : ℝ) (b i : ℝ) hq (NNReal.coe_nonneg _) habR
    calc
      ENNReal.ofReal (Real.exp (-(q * (a i : ℝ)))) ≤
          ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) +
            ENNReal.ofReal (q * ((b i : ℝ) - (a i : ℝ))) := hpoint
      _ ≤ ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) +
            ENNReal.ofReal (q * h) := by
        gcongr <;> exact hwidth
  obtain ⟨hLow, hHigh⟩ :=
    avram_p4_d_dividend_original_full_stieltjes_finite_mesh_discount_error
      D hD ω q hq s a b (fun _ => ENNReal.ofReal (q * h)) hab hdelta
  refine ⟨hLow, ?_⟩
  simpa only [Finset.mul_sum] using hHigh
