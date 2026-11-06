-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_strict_terminal_budgets_imply_closed_terminal_budgets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:29:28.544869+00:00
-- url     : https://prove2.me/submissions/4eca60cf-f8f1-4adf-8c1b-8d5bf043154f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Strict cash-plus-terminal budgets at n+1 imply closed budgets
    at n, retaining the original nonnegative terminal and time-zero atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hStrict : ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B) :
    ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B := by
  intro n
  obtain ⟨Terminal, hBound⟩ := hStrict n
  refine ⟨Terminal, ?_⟩
  calc
    _ ≤ (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
      apply lintegral_mono
      intro ω
      apply add_le_add_left
      apply lintegral_mono_set
      intro t ht
      have hn : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self n
      exact ⟨ht.1, lt_of_le_of_lt ht.2 hn⟩
    _ ≤ B := hBound
