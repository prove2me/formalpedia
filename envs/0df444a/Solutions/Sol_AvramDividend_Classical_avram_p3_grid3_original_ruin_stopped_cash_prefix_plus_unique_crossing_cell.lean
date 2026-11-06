-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cash_prefix_plus_unique_crossing_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:25:31.513206+00:00
-- url     : https://prove2.me/submissions/b43a6db6-7e99-4096-b44a-c2a808bb5cd4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_prefix_and_single_boundary_bridge
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original strict physical cash has exactly one positive-time crossing-cell remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) (q : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    0 < τ →
      ∃ k i : ℕ, k ≤ m + 1 ∧ u k < τ ∧
        i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        (∑ j ∈ Finset.range (m + 1), cash j) =
          (∑ j ∈ Finset.range k, cash j) + cash i := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let cash : ℕ → ℝ := fun i =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  change 0 < τ →
    ∃ k i : ℕ, k ≤ m + 1 ∧ u k < τ ∧
      i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
      (∑ j ∈ Finset.range (m + 1), cash j) =
        (∑ j ∈ Finset.range k, cash j) + cash i
  intro hτ
  obtain ⟨k, hk, hcash, hstrict⟩ :=
    avram_p3_grid3_original_ruin_stopped_cash_prefix_and_single_boundary_bridge
      X x D T m ω q
  obtain ⟨i, hi, hbelow, hhit, hsingle⟩ :=
    avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
      X x D T m ω hτ
  have hsplit : (∑ j ∈ Finset.range (m + 1), cash j) =
      (∑ j ∈ Finset.range k, cash j) + cash i := by
    change (∑ j ∈ Finset.range (m + 1), cash j) =
      (∑ j ∈ Finset.range k, cash j) +
        ∑ j ∈ (Finset.range (m + 1)).filter
          (fun j => u j < τ ∧ u (j + 1) = τ), cash j at hcash
    rw [hsingle] at hcash
    simpa using hcash
  exact ⟨k, i, hk, hstrict hτ, hi, hbelow, hhit, hsplit⟩
