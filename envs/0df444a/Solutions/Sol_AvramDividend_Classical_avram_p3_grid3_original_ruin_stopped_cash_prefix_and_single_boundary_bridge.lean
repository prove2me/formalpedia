-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cash_prefix_and_single_boundary_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:16:53.695706+00:00
-- url     : https://prove2.me/submissions/85d8c822-b505-401a-9d36-728445ed9c08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    ∃ k : ℕ, k ≤ m + 1 ∧
      ((∑ i ∈ Finset.range (m + 1), cash i) =
        (∑ i ∈ Finset.range k, cash i) +
        ∑ i ∈ (Finset.range (m + 1)).filter
          (fun i => u i < τ ∧ u (i + 1) = τ), cash i) ∧
      (0 < τ → u k < τ) := by
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
  change ∃ k : ℕ, k ≤ m + 1 ∧
    ((∑ i ∈ Finset.range (m + 1), cash i) =
      (∑ i ∈ Finset.range k, cash i) +
      ∑ i ∈ (Finset.range (m + 1)).filter
        (fun i => u i < τ ∧ u (i + 1) = τ), cash i) ∧
    (0 < τ → u k < τ)
  obtain ⟨k, hk, hprefix, hstrict⟩ :=
    avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
      X x D T m ω
  have hsplit :=
    avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
      X x D T m (m + 1) ω q
  change (∑ i ∈ Finset.range (m + 1), cash i) =
    (∑ i ∈ (Finset.range (m + 1)).filter
      (fun i => u (i + 1) < τ), cash i) +
    ∑ i ∈ (Finset.range (m + 1)).filter
      (fun i => u i < τ ∧ u (i + 1) = τ), cash i at hsplit
  rw [hprefix] at hsplit
  exact ⟨k, hk, hsplit, hstrict⟩
