-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_total_cash_equals_precontact_filter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:53:40.758194+00:00
-- url     : https://prove2.me/submissions/3a2d1581-c876-4729-ae41-71f9c5575648

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
      ∑ i ∈ (Finset.range n).filter (fun i => u i < τ), cash i := by
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
    ∑ i ∈ (Finset.range n).filter (fun i => u i < τ), cash i
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hBefore : u i < τ
  · simp [hBefore]
  · have hUi : u i = τ := by
      exact le_antisymm (min_le_right _ _)
        (le_of_not_gt hBefore)
    have hzero : cash i = 0 :=
      avram_p3_grid3_original_ruin_stopped_physical_cash_zero_after_contact
        X x D T m ω q i hUi
    simp [hBefore, hzero]
