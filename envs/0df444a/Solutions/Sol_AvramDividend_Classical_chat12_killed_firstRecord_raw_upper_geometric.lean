-- Prove2me | solution 1 for AvramDividend.Classical.chat12_killed_firstRecord_raw_upper_geometric
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:54:50.526253+00:00
-- url     : https://prove2.me/submissions/41b96cdd-08da-480f-b6c6-a3f9339e2aff

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_next_expected_le_current_mul_twoSided

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) :
    ∀ n : ℕ,
      (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
      (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ^ n * (∫⁻ ω, if twoSidedExitUpTime X ((0 : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((0 : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by
  let factor : ℝ≥0∞ := (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P)
  let reward : ℕ → ℝ≥0∞ := fun m => (∫⁻ ω, if twoSidedExitUpTime X ((m : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((m : ℝ) * ε) ω).toReal)))
      else 0 ∂P)
  have hstep (m : ℕ) : reward (m + 1) ≤ factor * reward m := by
    simpa only [factor, reward] using
      (killed_firstRecord_next_expected_le_current_mul_twoSided
        X hX q hq a ε ha hε m)
  have hgeom : ∀ n : ℕ, reward n ≤ factor ^ n * reward 0 := by
    intro n
    induction n with
    | zero =>
        simpa only [pow_zero, one_mul] using (le_refl (reward 0))
    | succ m ih =>
        have hmul : factor * reward m ≤
            factor * (factor ^ m * reward 0) := by
          gcongr <;> assumption
        calc
          reward (m + 1) ≤ factor * reward m := hstep m
          _ ≤ factor * (factor ^ m * reward 0) := hmul
          _ = factor ^ (m + 1) * reward 0 := by
            rw [pow_succ]
            ac_rfl
  intro n
  simpa only [factor, reward, Nat.cast_zero] using hgeom n
