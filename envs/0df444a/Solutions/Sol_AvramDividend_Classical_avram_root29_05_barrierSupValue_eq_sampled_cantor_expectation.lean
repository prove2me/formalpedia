-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_barrierSupValue_eq_sampled_cantor_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:20:36.924739+00:00
-- url     : https://prove2.me/submissions/b5ce9e80-b9a7-439d-afc0-c596089495eb

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_original_runningSup_stopped_reward_ignores_nonpositive_times
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_original_reflected_stieltjes_eq_sampled_cantor_reward
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The genuine reflected-supremum dividend value is the expectation of
the globally measurable stopped Cantor-record reward of the original path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (hq : 0 ≤ q) :
    barrierSupValue X a q =
      ∫⁻ ω : Ω,
        (let samples : ℕ → ℝ≥0 := fun j =>
           ((Nat.unpair j).2 : ℝ≥0) *
             (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let record : ℝ≥0 → ℝ := fun t =>
           (⨆ j : ℕ,
             if samples j ≤ t then
               ENNReal.ofReal (X.X (samples j) ω - X.X 0 ω) else 0).toReal
         let grid : ℕ → ℕ → ℝ≥0 := fun n k =>
           (k : ℝ≥0) * (((n + 1 : ℕ) : ℝ≥0)⁻¹)
         let ρ : ℝ≥0∞ := ⨅ i : ℕ,
           if X.X (samples i) ω - X.X 0 ω - record (samples i) < -a
           then (samples i : ℝ≥0∞) else ⊤
         ⨆ n : ℕ, ⨆ N : ℕ,
           ∑ k ∈ Finset.range N,
             if (grid n (k + 1) : ℝ≥0∞) < ρ then
               ENNReal.ofReal
                 (Real.exp (-(q * ((grid n (k + 1) : ℝ≥0) : ℝ)))) *
               ENNReal.ofReal
                 (record (grid n (k + 1)) - record (grid n k))
             else 0) ∂P := by
  unfold barrierSupValue
  apply lintegral_congr
  intro ω
  rw [avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock X a ω]
  rw [avram_root29_05_original_runningSup_stopped_reward_ignores_nonpositive_times
    X ω q _]
  exact avram_root29_05_original_reflected_stieltjes_eq_sampled_cantor_reward
    X ω a q hq
