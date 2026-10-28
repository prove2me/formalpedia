-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_sampled_levy_clock_top_iff_no_upcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:27:36.07124+00:00
-- url     : https://prove2.me/submissions/2e85cb76-8d99-4ff3-abbf-cbeee33e2c3c

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_top_iff_all_top
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-! A finite sampled upcrossing clock is infinite precisely without any sampled crossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P ℱ)
    (h : ℝ≥0) (a : ℝ) (n : ℕ) (ω : Ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω =>
        min (if a < X.X ((k : ℝ≥0) * h) ω
          then (((k : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
          (σ ω)) n) ω = ⊤ ↔
      ∀ k : ℕ, k < n → X.X ((k : ℝ≥0) * h) ω ≤ a := by
  rw [chat08_finite_minimum_clock_top_iff_all_top
    (fun k ω =>
      if a < X.X ((k : ℝ≥0) * h) ω
      then (((k : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤) n ω]
  constructor
  · intro hall k hk
    by_contra hnot
    have hlt : a < X.X ((k : ℝ≥0) * h) ω := lt_of_not_ge hnot
    have hclock := hall k hk
    simp [hlt] at hclock
    norm_cast at hclock
  · intro hle k hk
    have hnot : ¬ a < X.X ((k : ℝ≥0) * h) ω := not_lt.mpr (hle k hk)
    simp [hnot]
