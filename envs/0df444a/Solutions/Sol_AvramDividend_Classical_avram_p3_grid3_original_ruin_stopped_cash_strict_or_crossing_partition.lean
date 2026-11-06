-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:53:45.130379+00:00
-- url     : https://prove2.me/submissions/43f22eb9-73d8-4c4b-bdd0-e1268d7d5ae2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cash_zero_after_contact
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
    (T : ℝ≥0) (m n : ℕ) (ω : Ω) (q : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    (∑ i ∈ Finset.range n, cash i) =
      (∑ i ∈ (Finset.range n).filter
          (fun i => u (i + 1) < τ), cash i) +
      ∑ i ∈ (Finset.range n).filter
        (fun i => u i < τ ∧ u (i + 1) = τ), cash i := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun k =>
    min (((min k (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let cash : ℕ → ℝ := fun i =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  change (∑ i ∈ Finset.range n, cash i) =
    (∑ i ∈ (Finset.range n).filter
        (fun i => u (i + 1) < τ), cash i) +
    ∑ i ∈ (Finset.range n).filter
      (fun i => u i < τ ∧ u (i + 1) = τ), cash i
  have hpoint (i : ℕ) :
      cash i =
        (if u (i + 1) < τ then cash i else 0) +
        (if u i < τ ∧ u (i + 1) = τ then cash i else 0) := by
    by_cases hEnd : u (i + 1) < τ
    · have hNotCross :
          ¬ (u i < τ ∧ u (i + 1) = τ) := by
        intro hCross
        exact (ne_of_lt hEnd) hCross.2
      simp [hEnd, hNotCross]
    · have hEndEq : u (i + 1) = τ :=
        le_antisymm (min_le_right _ _)
          (le_of_not_gt hEnd)
      by_cases hStart : u i < τ
      · simp [hEnd, hStart, hEndEq]
      · have hStartEq : u i = τ :=
          le_antisymm (min_le_right _ _)
            (le_of_not_gt hStart)
        have hzero : cash i = 0 :=
          avram_p3_grid3_original_ruin_stopped_physical_cash_zero_after_contact
            X x D T m ω q i hStartEq
        simp [hEnd, hStart, hzero]
  calc
    (∑ i ∈ Finset.range n, cash i) =
        ∑ i ∈ Finset.range n,
          ((if u (i + 1) < τ then cash i else 0) +
            (if u i < τ ∧ u (i + 1) = τ then cash i else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpoint i
    _ = (∑ i ∈ (Finset.range n).filter
            (fun i => u (i + 1) < τ), cash i) +
          ∑ i ∈ (Finset.range n).filter
            (fun i => u i < τ ∧ u (i + 1) = τ), cash i := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_filter]
