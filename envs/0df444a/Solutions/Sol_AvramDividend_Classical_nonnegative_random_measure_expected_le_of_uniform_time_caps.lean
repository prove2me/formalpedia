-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_random_measure_expected_le_of_uniform_time_caps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T12:15:43.494906+00:00
-- url     : https://prove2.me/submissions/ac744be9-1f37-43f6-811d-6814ab9b1614

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_nonnegative_random_measure_time_horizon_lintegral_iSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped Classical ENNReal
open AvramDividend.Classical

/-- A uniform bound on the expected payouts over finite horizons controls the full random-measure payout. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (μ : Ω → Measure ℝ)
    (f : Ω → ℝ → ℝ≥0∞)
    (hf : ∀ ω, Measurable (f ω))
    (hMeas : ∀ n : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in Icc (0 : ℝ) (n : ℝ), f ω t ∂(μ ω)))
    (K : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, (∫⁻ t in Icc (0 : ℝ) (n : ℝ),
        f ω t ∂(μ ω)) ∂P) ≤ K) :
    (∫⁻ ω, (∫⁻ t in Ici (0 : ℝ), f ω t ∂(μ ω)) ∂P) ≤ K := by
  rw [nonnegative_random_measure_time_horizon_lintegral_iSup P μ f hf hMeas]
  exact iSup_le hBound
