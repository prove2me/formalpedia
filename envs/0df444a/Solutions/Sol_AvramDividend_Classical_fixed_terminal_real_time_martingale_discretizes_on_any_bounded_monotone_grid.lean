-- Prove2me | solution 1 for AvramDividend.Classical.fixed_terminal_real_time_martingale_discretizes_on_any_bounded_monotone_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:26:12.797694+00:00
-- url     : https://prove2.me/submissions/0ffe7bc3-ec1a-4c70-add6-bed099486a98

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_exists_nat_filtration_along_monotone_nonnegative_time_grid
open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ n : ℕ, g n ≤ T)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : ℝ≥0 → Ω → ℝ)
    (hadapt : ∀ t : ℝ≥0, StronglyMeasurable[𝓕 t] (Z t))
    (hint : ∀ n : ℕ, Integrable (Z (g n)) μ)
    (hevents : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      ∀ A : Set Ω, @MeasurableSet Ω (𝓕 s) A →
      (∫ ω in A, Z s ω ∂μ) = (∫ ω in A, Z t ω ∂μ)) :
    ∃ 𝓖 : Filtration ℕ mΩ,
      (∀ n : ℕ, 𝓖 n = 𝓕 (g n)) ∧
      Martingale (fun n ω => Z (g n) ω) 𝓖 μ := by
  obtain ⟨𝓖, h𝓖⟩ := AvramDividend.Classical.exists_nat_filtration_along_monotone_nonnegative_time_grid 𝓕 g hg
  refine ⟨𝓖, h𝓖, ?_⟩
  refine martingale_of_setIntegral_eq_succ (fun n => ?_) hint (fun i s hs => ?_)
  · rw [h𝓖 n]; exact hadapt (g n)
  · rw [h𝓖 i] at hs
    exact hevents (g i) (g (i + 1)) (hg (Nat.le_succ i)) (hgT _) s hs
