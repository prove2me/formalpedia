-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_finiteGrid_positive_martingale_consumption_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:33:01.338684+00:00
-- url     : https://prove2.me/submissions/342748e4-df09-4e7b-bfd2-92ee30665503

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝓕 μ)
    (hMpos : ∀ t ω, 0 ≤ M t ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : Adapted 𝓕 B)
    (hBbound : ∀ t ω, 0 ≤ B t ω ∧ B t ω ≤ 1)
    (hBanti : ∀ ω, Antitone (fun t => B t ω))
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∀ ω, 0 ≤ ∑ i ∈ Finset.range n,
      M (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)) ∧
    (∫ ω, ∑ i ∈ Finset.range n,
      M (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) ∂μ) ≤
      (∫ ω, B (u 0) ω * M (u 0) ω ∂μ) := by
  constructor
  · intro ω
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (hMpos (u (i + 1)) ω)
    exact sub_nonneg.mpr (hBanti ω (hu (Nat.le_succ i)))
  · have heq :=
      avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance
        M hM B hB hBbound u hu n
    rw [heq]
    have hterminal :
        0 ≤ (∫ ω, B (u n) ω * M (u n) ω ∂μ) := by
      apply integral_nonneg
      intro ω
      exact mul_nonneg (hBbound (u n) ω).1 (hMpos (u n) ω)
    linarith
