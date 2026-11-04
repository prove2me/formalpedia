-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:33:44.625823+00:00
-- url     : https://prove2.me/submissions/eead7d3b-0685-4a24-8d76-4ad9544f08c5

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact source Stieltjes mass controls any bounded payment-time cell weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (lo hi : ℝ≥0∞) (f : ℝ → ℝ≥0∞)
    (hlo : ∀ u ∈ Ioc (a : ℝ) (b : ℝ), lo ≤ f u)
    (hhi : ∀ u ∈ Ioc (a : ℝ) (b : ℝ), f u ≤ hi) :
    lo * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      (∫⁻ u in Ioc (a : ℝ) (b : ℝ), f u ∂(dividendMeasure D ω)) ∧
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ), f u ∂(dividendMeasure D ω)) ≤
      hi * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by
  let μ := dividendMeasure D ω
  let s : Set ℝ := Ioc (a : ℝ) (b : ℝ)
  have hs : MeasurableSet s := measurableSet_Ioc
  have hmem : ∀ᵐ u ∂μ.restrict s, u ∈ s := ae_restrict_mem hs
  have hLow : (∫⁻ u in s, lo ∂μ) ≤ (∫⁻ u in s, f u ∂μ) := by
    apply lintegral_mono_ae
    filter_upwards [hmem] with u hu
    exact hlo u hu
  have hHigh : (∫⁻ u in s, f u ∂μ) ≤ (∫⁻ u in s, hi ∂μ) := by
    apply lintegral_mono_ae
    filter_upwards [hmem] with u hu
    exact hhi u hu
  constructor
  · calc
      lo * μ s = ∫⁻ u in s, lo ∂μ := by simp [lintegral_const, mul_comm]
      _ ≤ ∫⁻ u in s, f u ∂μ := hLow
  · calc
      (∫⁻ u in s, f u ∂μ) ≤ (∫⁻ u in s, hi ∂μ) := hHigh
      _ = hi * μ s := by simp [lintegral_const, mul_comm]
