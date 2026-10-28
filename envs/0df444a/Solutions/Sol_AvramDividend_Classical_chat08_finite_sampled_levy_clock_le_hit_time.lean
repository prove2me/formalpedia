-- Prove2me | solution 1 for AvramDividend.Classical.chat08_finite_sampled_levy_clock_le_hit_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:33:51.39809+00:00
-- url     : https://prove2.me/submissions/b34126f8-ae60-479c-8b64-d3934e646be3

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_le_any_included_observation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-! A recorded Lévy upcrossing bounds the finite first-passage clock by its grid time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P ℱ)
    (h : ℝ≥0) (a : ℝ) (n k : ℕ) (hk : k < n) (ω : Ω)
    (hhit : a < X.X ((k : ℝ≥0) * h) ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω =>
        min (if a < X.X ((j : ℝ≥0) * h) ω
          then (((j : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
          (σ ω)) n) ω ≤
      (((k : ℝ≥0) * h) : WithTop ℝ≥0) := by
  have hmin := chat08_finite_minimum_le_any_included_observation
    (fun j ω =>
      if a < X.X ((j : ℝ≥0) * h) ω
      then (((j : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
    n k hk ω
  simpa only [if_pos hhit] using hmin
