-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_unbounded_killed_grid_ost_all_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:21:07.385889+00:00
-- url     : https://prove2.me/submissions/36c92251-86c7-4cdf-bb94-ae98a2ea21d8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_grid_ost_from_source
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_zero_of_negative_initial_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine UBV killed-scale bounded-grid stopping identity extends to
all real starting reserves, with the negative-reserve payoff identically zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q x : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
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
  by_cases hx : 0 ≤ x
  · exact avram_root29_01_unbounded_killed_grid_ost_from_source
      X hnbv q x hq W hW hx clock hc hclock0 lower upper m
  · have hxNeg : x < 0 := lt_of_not_ge hx
    have hWx : W x = 0 := hW.1 x hxNeg
    have hpoint (ω : Ω) :
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
            (Set.Ioi (0 : ℝ)) 0 m ω)) ω)) ω = 0 := by
      exact chat04_killed_scale_payoff_zero_of_negative_initial_reserve
        X q x hxNeg W
        (clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω)) ω
    simpa only [hpoint, integral_zero, hWx]
