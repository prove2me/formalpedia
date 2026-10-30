-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_raw_future_stieltjes_eq_cantor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:33:17.37037+00:00
-- url     : https://prove2.me/submissions/bfb8ff65-57cc-4775-9b4c-566d4934f875

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_future_raw_ruin_eq_strict_drawdown_subtype_clock
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_paymentTimes_Ioi_integral_eq_positive_weight
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_reflected_stieltjes_eq_sampled_cantor_reward
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The exact raw future-ruin stopped Stieltjes integral appearing after
upcrossing is the same measurable Cantor-sampled future reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (a q : ℝ) (hq : 0 ≤ q) :
    (let M : ℝ≥0 → ℝ := fun t =>
       sSup ((fun v : ℝ≥0 => X.X (age + v) ω - X.X age ω) '' Set.Icc 0 t)
     let raw : ℝ≥0∞ := ⨅ (t : ℝ≥0)
       (_ : a + (X.X (age + t) ω - X.X age ω) <
         max 0 (sSup ((fun v : ℝ≥0 => X.X (age + v) ω) '' Set.Icc 0 t) - X.X age ω)),
       (t : ℝ≥0∞)
     ∫⁻ t in Set.Ioi (0 : ℝ) ∩ paymentTimes raw,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂
       (dividendMeasure (fun t (_ : Ω) => M t) ω)) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (age + t) ω - X.X age ω
     let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let record : ℝ≥0 → ℝ := fun t =>
       (⨆ j : ℕ, if samples j ≤ t then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal
     let grid : ℕ → ℕ → ℝ≥0 := fun n k =>
       (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
     let ρ : ℝ≥0∞ := ⨅ i : ℕ, if f (samples i) - f 0 - record (samples i) < -a
       then (samples i : ℝ≥0∞) else ⊤
     ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
       if (grid n (k + 1) : ℝ≥0∞) < ρ then
         ENNReal.ofReal (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
         ENNReal.ofReal (record (grid n (k + 1)) - record (grid n k)) else 0) := by
  let M : ℝ≥0 → ℝ := fun t =>
    sSup ((fun v : ℝ≥0 => X.X (age + v) ω - X.X age ω) '' Icc 0 t)
  let μ : Measure ℝ := dividendMeasure (fun t (_ : Ω) => M t) ω
  let raw : ℝ≥0∞ := ⨅ (t : ℝ≥0)
    (_ : a + (X.X (age + t) ω - X.X age ω) <
      max 0 (sSup ((fun v : ℝ≥0 => X.X (age + v) ω) '' Icc 0 t) - X.X age ω)),
    (t : ℝ≥0∞)
  let τ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
    (X.X (age + t) ω - X.X age ω) - M t < -a}, (i.1 : ℝ≥0∞)
  have hclock : raw = τ := by
    simpa [raw, τ, M] using
      avram_root29_05_shifted_future_raw_ruin_eq_strict_drawdown_subtype_clock X ω age a
  have hsample := avram_root29_05_shifted_reflected_stieltjes_eq_sampled_cantor_reward
    X ω age a q hq
  change (∫⁻ t in Ioi (0 : ℝ) ∩ paymentTimes raw,
    ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) = _
  rw [hclock]
  exact (avram_root29_05_paymentTimes_Ioi_integral_eq_positive_weight
    μ τ (fun t => ENNReal.ofReal (Real.exp (-(q * t))))).trans hsample
