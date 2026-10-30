-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_killed_scale_grid_optional_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:59:00.31046+00:00
-- url     : https://prove2.me/submissions/e0e3cdbf-563c-41f6-9c7f-f726b18b67cc

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_grid_optional_stopping_of_martingale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- Actual BV killed-scale bounded-grid optional stopping at the true Lévy reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) (hx : 0 ≤ x)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (hclock0 : clock 0 = 0)
    (lower upper : ℝ) (m : ℕ) :
    (∫ ω,
      ({ω | ∀ s : ℝ≥0,
        s ≤ clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω) →
          0 ≤ x + X.X s ω}).indicator
      (fun ω =>
        Real.exp (-(q * (clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω) : ℝ))) *
        W (x + X.X (clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω)) ω)) ω ∂P) = W x := by
  have hKilled := avram_ws01b_bv_killed_scale_martingale X hX q hq W hW hBV x
  exact chat03_killed_scale_grid_optional_stopping_of_martingale
    X q x W hx hKilled clock hc hclock0 lower upper m
