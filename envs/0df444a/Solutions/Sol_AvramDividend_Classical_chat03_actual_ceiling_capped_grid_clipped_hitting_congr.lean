-- Prove2me | solution 1 for AvramDividend.Classical.chat03_actual_ceiling_capped_grid_clipped_hitting_congr
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:36:49.830714+00:00
-- url     : https://prove2.me/submissions/f9ca859e-9581-412c-9c30-e7552c25e61a

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_congr_before_terminal
import Theorems.Thm_AvramDividend_Classical_chat03_ceiling_grid_preterminal_lt
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
The actual (unclipped) uniform-grid first-hitting index equals the
first-hitting index observed at horizon-clipped times. Every sample
strictly before the terminal ceiling index lies below the horizon.
The terminal index itself cannot affect the returned bounded clock.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (T h : ℝ≥0) (hh : 0 < h) (ω : Ω) :
    hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * h) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * h) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / h)) ω =
    hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X (min ((j : ℝ≥0) * h) T) ξ - upper)
        (lower - X.X (min ((j : ℝ≥0) * h) T) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / h)) ω := by
  apply chat03_hittingBtwn_congr_before_terminal
  intro j hj
  have hlt : (j : ℝ≥0) * h < T :=
    chat03_ceiling_grid_preterminal_lt T h hh j hj
  simp only [min_eq_left (le_of_lt hlt)]
