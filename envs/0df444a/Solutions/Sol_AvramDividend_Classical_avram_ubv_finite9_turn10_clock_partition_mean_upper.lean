-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn10_clock_partition_mean_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:27:41.643085+00:00
-- url     : https://prove2.me/submissions/23787873-12a2-4b0e-aa0a-525de8c0cec7

import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A stopped integrable reward whose positive-clock mean is at most the
probability-weighted benchmark, and whose zero-clock reward is pointwise at
most that benchmark, has full mean at most the benchmark. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (b : ℝ) (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hzeroMeas : MeasurableSet {ω : Ω | σ ω = 0})
    (hFI : Integrable F P)
    (hzero : ∀ ω, σ ω = 0 → F ω ≤ b)
    (hpositive : (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω ∂P) ≤
      b * (P {ω : Ω | σ ω ≠ 0}).toReal) :
    (∫ ω, F ω ∂P) ≤ b := by
  let A : Set Ω := {ω : Ω | σ ω ≠ 0}
  have hA : MeasurableSet A := by
    simpa [A, Set.compl_setOf] using hzeroMeas.compl
  have hZeroMean :
      (∫ ω in Aᶜ, F ω ∂P) ≤ b * P.real Aᶜ := by
    have hOn := setIntegral_mono_on
      (hFI.integrableOn (s := Aᶜ))
      ((integrable_const b).integrableOn (s := Aᶜ))
      hA.compl (by
        intro ω hω
        exact hzero ω (by simpa [A] using hω))
    calc
      (∫ ω in Aᶜ, F ω ∂P) ≤ ∫ _ in Aᶜ, b ∂P := hOn
      _ = b * P.real Aᶜ := by rw [setIntegral_const]; simp [smul_eq_mul, mul_comm]
  have hProb : P.real A + P.real Aᶜ = 1 :=
    probReal_add_probReal_compl hA
  have hPositive : (∫ ω in A, F ω ∂P) ≤ b * P.real A := by
    simpa [A, Measure.real] using hpositive
  calc
    (∫ ω, F ω ∂P) = (∫ ω in A, F ω ∂P) +
        (∫ ω in Aᶜ, F ω ∂P) :=
      (integral_add_compl hA hFI).symm
    _ ≤ b * P.real A + b * P.real Aᶜ := add_le_add hPositive hZeroMean
    _ = b := by rw [← mul_add, hProb, mul_one]
