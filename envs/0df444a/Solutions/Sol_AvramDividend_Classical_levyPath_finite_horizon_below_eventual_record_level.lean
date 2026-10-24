-- Prove2me | solution 1 for AvramDividend.Classical.levyPath_finite_horizon_below_eventual_record_level
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:40:08.904908+00:00
-- url     : https://prove2.me/submissions/69bfe299-eb69-493a-b5df-cb2960ba95df

import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! A finite sample-path horizon meets only finitely many positive-width record levels. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (ω : Ω)
    (T : ℝ≥0) (b h : ℝ) (hh : 0 < h) :
    ∃ N : ℕ, ∀ t : ℝ≥0, t ≤ T →
      X.X t ω < b + (N : ℝ) * h := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((runningSup X T ω - b) / h)
  refine ⟨N, ?_⟩
  intro t ht
  have hp := (runningSup_monotone_and_path_le X ω)
  have hXt : X.X t ω ≤ runningSup X T ω := (hp.2 t).trans (hp.1 ht)
  have hm := mul_lt_mul_of_pos_right hN hh
  have hcancel : ((runningSup X T ω - b) / h) * h =
      runningSup X T ω - b := div_mul_cancel₀ _ (ne_of_gt hh)
  rw [hcancel] at hm
  linarith
