-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:49:18.962812+00:00
-- url     : https://prove2.me/submissions/dea1de5f-58fd-49c1-a92b-acaff1e7df79

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact finite-grid zero-mean expectation for a simple predictable
integrand against centered original Lévy future increment payoffs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι)
    (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ S, Measurable (φ i))
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (H i))
    (K : ι → ℝ)
    (hBound : ∀ i ∈ S, ∀ ω, ‖H i ω‖ ≤ K i)
    (hInt : ∀ i ∈ S,
      Integrable (fun ω => φ i (X.X (t i - s i) ω)) P)
    (hmean : ∀ i ∈ S,
      (∫ ω, φ i (X.X (t i - s i) ω) ∂P) = 0) :
    (∫ ω, ∑ i ∈ S, H i ω *
      φ i (X.X (t i) ω - X.X (s i) ω) ∂P) = 0 := by
  have hTermInt (i : ι) (hi : i ∈ S) :
      Integrable
        (fun ω => H i ω * φ i (X.X (t i) ω - X.X (s i) ω)) P := by
    have hIdent : IdentDistrib
        (fun ω => φ i (X.X (t i) ω - X.X (s i) ω))
        (fun ω => φ i (X.X (t i - s i) ω)) P P := by
      simpa only [Function.comp_def] using
        (X.stationaryIncrements (s i) (t i) (hst i hi)).comp (hφ i hi)
    have hInc : Integrable
        (fun ω => φ i (X.X (t i) ω - X.X (s i) ω)) P :=
      hIdent.integrable_iff.mpr (hInt i hi)
    exact hInc.bdd_mul
      ((hH i hi).mono (𝓕.le (s i))).aestronglyMeasurable
      (Filter.Eventually.of_forall (hBound i hi))
  have hEq := integral_finset_sum S hTermInt
  rw [hEq]
  apply Finset.sum_eq_zero
  intro i hi
  exact avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero
    X (s i) (t i) (hst i hi) (φ i) (hφ i hi)
    (H i) (hH i hi) (K i) (hBound i hi)
    (hInt i hi) (hmean i hi)
