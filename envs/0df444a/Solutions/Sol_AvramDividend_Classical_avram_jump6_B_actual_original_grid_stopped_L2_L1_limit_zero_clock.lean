-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_original_grid_stopped_L2_L1_limit_zero_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:42:02.303994+00:00
-- url     : https://prove2.me/submissions/732ca328-5c83-4797-b672-21fbdddf5ebb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_predictable_grid_energy_L2_to_eventwise_L1_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_gbB54zz_event_restricted_zero_L1_limit_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (W : ℕ → ℕ → Ω → ℝ)
    (hWPast : ∀ k, ∀ i ∈ Finset.range (n k),
      Measurable[𝓕 (s k i)] (W k i))
    (hWI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (W k i) P)
    (hXI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (X.X (t k i)) P)
    (hCellI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (fun ω =>
      W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
        (∫ η, X.X (t k i) η ∂P))) P)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSource : ∀ k, (M k : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n k),
        W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
          (∫ η, X.X (t k i) η ∂P)))
    (Cband : ℝ)
    (hBandBound : ∀ i j : ℕ, i ≤ j →
      dist (M i) (M j) ≤
        Cband * Real.sqrt ((∫⁻ z in Ioc (-(1 / ((i : ℝ) + 1))) (0 : ℝ),
          ENNReal.ofReal (z ^ 2) ∂X.ν).toReal))
    (clock : Ω → ℝ≥0)
    (hClockMeas : MeasurableSet {ω : Ω | clock ω = 0})
    (hGridZero : ∀ j ω, clock ω = 0 → (M j : Ω → ℝ) ω = 0) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 ∧
      ∀ A : Set Ω,
        Tendsto (fun j : ℕ =>
          ∫ ω in A, |L ω - M j ω| ∂P)
          atTop (𝓝 (0 : ℝ)) ∧
      (∀ᵐ ω ∂P, clock ω = 0 → L ω = 0) := by
  obtain ⟨L, hLim, hMean, hEvent⟩ :=
    avram_jump6_B_original_predictable_grid_energy_L2_to_eventwise_L1_zero_mean
      X n s t W hWPast hWI hXI hCellI M hSource Cband hBandBound
  refine ⟨L, hLim, hMean, ?_⟩
  intro A
  refine ⟨hEvent A, ?_⟩
  have hLInt : Integrable (L : Ω → ℝ) P :=
    MemLp.integrable (by norm_num) (Lp.memLp L)
  have hMI : ∀ j, Integrable (M j : Ω → ℝ) P := by
    intro j
    exact MemLp.integrable (by norm_num) (Lp.memLp (M j))
  have hFull : Tendsto
      (fun j : ℕ => ∫ ω, |L ω - M j ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [MeasureTheory.setIntegral_univ] using hEvent Set.univ
  exact avram_gbB54zz_event_restricted_zero_L1_limit_ae
    P {ω : Ω | clock ω = 0} hClockMeas
    (fun ω => L ω) (fun j ω => M j ω)
    hLInt hMI hGridZero hFull
