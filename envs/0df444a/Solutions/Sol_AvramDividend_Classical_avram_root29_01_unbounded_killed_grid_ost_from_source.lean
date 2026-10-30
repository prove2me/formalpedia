-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_unbounded_killed_grid_ost_from_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:11:42.785556+00:00
-- url     : https://prove2.me/submissions/c980a166-27aa-4ebb-99ec-d754fa8b1c99

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_martingale_from_source
import Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_grid_optional_stopping_of_martingale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual UBV killed q-scale martingale has the authentic
bounded-grid optional-stopping expectation, including survival history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q x : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hx : 0 ≤ x)
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
  have hKilled :=
    avram_root29_01_unbounded_killed_martingale_from_source
      X hnbv q hq W hW x
  exact chat03_killed_scale_grid_optional_stopping_of_martingale
    X q x W hx hKilled clock hc hclock0 lower upper m
