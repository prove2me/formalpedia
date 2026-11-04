-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_finite_mesh_discount_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:10:50.350036+00:00
-- url     : https://prove2.me/submissions/d858b4fd-923a-4f04-8e43-6cadacd0cd42

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cell_uniform_weight_error

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original discounted Stieltjes cash on a finite mesh is within a cell-oscillation budget. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (s : Finset ι) (a b : ι → ℝ≥0) (δ : ι → ℝ≥0∞)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hδ : ∀ i ∈ s,
      ENNReal.ofReal (Real.exp (-(q * (a i : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) + δ i) :
    (∑ i ∈ s, ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
      dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) ≤
    (∑ i ∈ s, ∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ∧
    (∑ i ∈ s, ∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ≤
      (∑ i ∈ s, ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
        dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) +
      (∑ i ∈ s, δ i * dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by
  have hcell (i : ι) (hi : i ∈ s) :
      ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
        dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ)) ≤
        (∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
          ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ∧
      (∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
        ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
          dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ)) +
        δ i * dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ)) := by
    apply avram_p4_d_dividend_original_full_stieltjes_cell_uniform_weight_error
      D hD ω (a i) (b i)
      (ENNReal.ofReal (Real.exp (-(q * (b i : ℝ))))) (δ i)
      (fun u => ENNReal.ofReal (Real.exp (-(q * u))))
    · intro u hu
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hu.2 hq
      linarith
    · intro u hu
      apply le_trans (b := ENNReal.ofReal (Real.exp (-(q * (a i : ℝ)))))
      · apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left (le_of_lt hu.1) hq
        linarith
      · exact hδ i hi
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact (hcell i hi).1
  · calc
      (∑ i ∈ s, ∫⁻ u in Ioc (a i : ℝ) (b i : ℝ),
        ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ≤
          ∑ i ∈ s, (ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
            dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ)) +
            δ i * dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by
              apply Finset.sum_le_sum
              intro i hi
              exact (hcell i hi).2
      _ = (∑ i ∈ s, ENNReal.ofReal (Real.exp (-(q * (b i : ℝ)))) *
            dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) +
          (∑ i ∈ s, δ i * dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by
              simp only [Finset.sum_add_distrib]
