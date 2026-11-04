-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_cell_uniform_weight_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:42:16.989372+00:00
-- url     : https://prove2.me/submissions/dafa3d4a-b712-44d1-bd8b-c733aab31e90

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Uniform deviations of a payment-time weight bound the exact original Stieltjes cash error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (lo δ : ℝ≥0∞) (f : ℝ → ℝ≥0∞)
    (hlo : ∀ u ∈ Ioc (a : ℝ) (b : ℝ), lo ≤ f u)
    (hhi : ∀ u ∈ Ioc (a : ℝ) (b : ℝ), f u ≤ lo + δ) :
    lo * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      (∫⁻ u in Ioc (a : ℝ) (b : ℝ), f u ∂(dividendMeasure D ω)) ∧
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ), f u ∂(dividendMeasure D ω)) ≤
      lo * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) +
        δ * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by
  obtain ⟨hLow, hHigh⟩ :=
    avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich
      D hD ω a b lo (lo + δ) f hlo hhi
  refine ⟨hLow, ?_⟩
  calc
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ), f u ∂(dividendMeasure D ω)) ≤
        (lo + δ) * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := hHigh
    _ = lo * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) +
          δ * dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by rw [add_mul]
