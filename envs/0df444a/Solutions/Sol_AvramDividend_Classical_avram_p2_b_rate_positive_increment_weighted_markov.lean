-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_positive_increment_weighted_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:44:44.664889+00:00
-- url     : https://prove2.me/submissions/29ad2720-1eb0-4f7e-9dfb-85446900209c

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y)
    (θ R : ℝ) (hR : 1 < R) (k : ℕ)
    (hInt : Integrable
      (fun ω => (Real.exp (θ * Y ω)) ^ k *
        (Real.exp (θ * Y ω) - 1) ^ 4) μ) :
    ENNReal.ofReal (R ^ k * (R - 1) ^ 4) *
      μ {ω | R ≤ Real.exp (θ * Y ω)} ≤
    ENNReal.ofReal
      (∫ ω, (Real.exp (θ * Y ω)) ^ k *
        (Real.exp (θ * Y ω) - 1) ^ 4 ∂μ) := by
  let g : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal ((Real.exp (θ * Y ω)) ^ k *
      (Real.exp (θ * Y ω) - 1) ^ 4)
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hs :
      {ω | R ≤ Real.exp (θ * Y ω)} ⊆
        {ω | ENNReal.ofReal (R ^ k * (R - 1) ^ 4) ≤ g ω} := by
    intro ω hω
    change R ≤ Real.exp (θ * Y ω) at hω
    apply ENNReal.ofReal_le_ofReal
    have hp : R ^ k ≤ (Real.exp (θ * Y ω)) ^ k := by
      gcongr
    have hw : (R - 1) ^ 4 ≤ (Real.exp (θ * Y ω) - 1) ^ 4 := by
      gcongr
    exact mul_le_mul hp hw (by positivity) (by positivity)
  have hn : ∀ᵐ ω ∂μ,
      0 ≤ (Real.exp (θ * Y ω)) ^ k *
        (Real.exp (θ * Y ω) - 1) ^ 4 :=
    Filter.Eventually.of_forall (fun ω => by positivity)
  have heq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hn
  calc
    _ ≤ ENNReal.ofReal (R ^ k * (R - 1) ^ 4) *
        μ {ω | ENNReal.ofReal (R ^ k * (R - 1) ^ 4) ≤ g ω} := by
      gcongr
    _ ≤ ∫⁻ ω, g ω ∂μ :=
      MeasureTheory.mul_meas_ge_le_lintegral hg
        (ENNReal.ofReal (R ^ k * (R - 1) ^ 4))
    _ = _ := heq.symm
