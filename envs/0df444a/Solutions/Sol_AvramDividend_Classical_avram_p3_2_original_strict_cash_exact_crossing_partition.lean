-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_cash_exact_crossing_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:06:35.107143+00:00
-- url     : https://prove2.me/submissions/5d748308-f6a0-472a-8d5b-cc7f60a9f190

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_card_exact
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped discounted cash partition has exactly the
strict pre-contact prefix and its single physical crossing cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (m : ℕ) (ω : Ω) (q : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let cash : ℕ → ℝ := fun j =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u j : ℝ) (u (j + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    0 < τ →
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        (∑ j ∈ Finset.range (m + 1), cash j) =
          (∑ j ∈ Finset.range i, cash j) + cash i := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let cash : ℕ → ℝ := fun j =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u j : ℝ) (u (j + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  change 0 < τ →
    ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
      (∑ j ∈ Finset.range (m + 1), cash j) =
        (∑ j ∈ Finset.range i, cash j) + cash i
  intro hτ
  obtain ⟨i, hi, hUi, hUi1, hCard⟩ :=
    avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
      X x D T m ω hτ
  change ((Finset.range (m + 1)).filter
    (fun j => u (j + 1) < τ)).card = i at hCard
  have hPrefix :=
    (avram_p3_grid3_original_ruin_stopped_strict_prefix_card_exact
      X x D T m ω).2
  change ((Finset.range (m + 1)).filter
      (fun j => u (j + 1) < τ)) =
    Finset.range (((Finset.range (m + 1)).filter
      (fun j => u (j + 1) < τ)).card) at hPrefix
  rw [hCard] at hPrefix
  obtain ⟨j, hj, hUj, hUj1, hSingleton⟩ :=
    avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
      X x D T m ω hτ
  have himem : i ∈ (Finset.range (m + 1)).filter
      (fun k => u k < τ ∧ u (k + 1) = τ) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ⟨hUi, hUi1⟩⟩
  change ((Finset.range (m + 1)).filter
    (fun k => u k < τ ∧ u (k + 1) = τ)) = ({j} : Finset ℕ)
    at hSingleton
  rw [hSingleton] at himem
  have hij : i = j := by simpa only [Finset.mem_singleton] using himem
  have hCross : ((Finset.range (m + 1)).filter
      (fun k => u k < τ ∧ u (k + 1) = τ)) = ({i} : Finset ℕ) := by
    simpa only [hij] using hSingleton
  have hPartition :=
    avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
      X x D T m (m + 1) ω q
  change (∑ k ∈ Finset.range (m + 1), cash k) =
    (∑ k ∈ (Finset.range (m + 1)).filter
      (fun k => u (k + 1) < τ), cash k) +
    (∑ k ∈ (Finset.range (m + 1)).filter
      (fun k => u k < τ ∧ u (k + 1) = τ), cash k) at hPartition
  rw [hPrefix, hCross] at hPartition
  refine ⟨i, hi, hUi, hUi1, ?_⟩
  simpa using hPartition
