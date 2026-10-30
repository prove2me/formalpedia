-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_dividendValue_eq_killed_cantor_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:39:13.957778+00:00
-- url     : https://prove2.me/submissions/29e0a379-c4d1-4ca2-9a90-9a6fe73b7e0b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_expected_futureRuin_stoppedReward
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_raw_future_stieltjes_eq_cantor
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The original strategy's expected killed Stieltjes dividends are the
actual first-upcrossing-discounted countable future-record reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x a : ℝ)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) (hq : 0 ≤ q) :
    dividendValue X q x (barrierStrategy X x a) =
    (let T := twoSidedExitUpTime X (a - x)
     let R := ruinTime X x (barrierStrategy X x a)
     let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let grid : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
     ∫⁻ ω, if T ω < R ω then
       ENNReal.ofReal (Real.exp (-(q * ((T ω).toNNReal : ℝ)))) *
       (let f : ℝ≥0 → ℝ := fun t =>
          X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω
        let record : ℝ≥0 → ℝ := fun t =>
          (⨆ j : ℕ, if samples j ≤ t then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal
        let ρ : ℝ≥0∞ := ⨅ i : ℕ, if f (samples i) - f 0 - record (samples i) < -a
          then (samples i : ℝ≥0∞) else ⊤
        ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
          if (grid n (k + 1) : ℝ≥0∞) < ρ then
            ENNReal.ofReal (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
            ENNReal.ofReal (record (grid n (k + 1)) - record (grid n k)) else 0)
     else 0 ∂P) := by
  let T := twoSidedExitUpTime X (a - x)
  let R := ruinTime X x (barrierStrategy X x a)
  let L : Ω → ℝ≥0∞ := fun ω =>
    ⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)
  rw [dividendValue_barrierStrategy_expected_futureRuin_stoppedReward X q x a ha hx0 hxa]
  apply lintegral_congr
  intro ω
  have hevent : T ω < R ω ↔ T ω < L ω := by
    simpa only [T, R, L, twoSidedExitUpTime] using
      barrierStrategy_upExit_before_controlledRuin_iff_rawExit X x a ha hx0 hxa ω
  change (if T ω < L ω then
    ENNReal.ofReal (Real.exp (-(q * ((T ω).toNNReal : ℝ)))) *
    (∫⁻ t in Ioi (0 : ℝ) ∩ paymentTimes
      (⨅ (r : ℝ≥0)
        (_ : a + (X.X ((T ω).toNNReal + r) ω - X.X ((T ω).toNNReal) ω) <
          max 0 (sSup ((fun v : ℝ≥0 =>
            X.X ((T ω).toNNReal + v) ω) '' Icc 0 r) -
              X.X ((T ω).toNNReal) ω)), (r : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂
        (dividendMeasure (fun t (_ : Ω) =>
          sSup ((fun v : ℝ≥0 =>
            X.X ((T ω).toNNReal + v) ω - X.X ((T ω).toNNReal) ω) '' Icc 0 t)) ω))
    else 0) =
    (if T ω < R ω then
      ENNReal.ofReal (Real.exp (-(q * ((T ω).toNNReal : ℝ)))) *
      (let f : ℝ≥0 → ℝ := fun t =>
         X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω
       let samples : ℕ → ℝ≥0 := fun j =>
         ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
       let record : ℝ≥0 → ℝ := fun t =>
         (⨆ j : ℕ, if samples j ≤ t then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal
       let grid : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
       let ρ : ℝ≥0∞ := ⨅ i : ℕ, if f (samples i) - f 0 - record (samples i) < -a
         then (samples i : ℝ≥0∞) else ⊤
       ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
         if (grid n (k + 1) : ℝ≥0∞) < ρ then
           ENNReal.ofReal (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
           ENNReal.ofReal (record (grid n (k + 1)) - record (grid n k)) else 0)
     else 0)
  by_cases h : T ω < L ω
  · rw [if_pos h, if_pos (hevent.mpr h)]
    exact congrArg (fun y : ℝ≥0∞ =>
      ENNReal.ofReal (Real.exp (-(q * ((T ω).toNNReal : ℝ)))) * y)
      (avram_root29_05_raw_future_stieltjes_eq_cantor
        X ω (T ω).toNNReal a q hq)
  · rw [if_neg h, if_neg (fun hR => h (hevent.mp hR))]
