-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_killed_bounded_grid_reward_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:57:57.797986+00:00
-- url     : https://prove2.me/submissions/893cf966-ee80-4965-bb00-210a622ceb52

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_killed_scale_grid_optional_stopping
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_bv_scale_origin_eq_inv_drift
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Actual bounded-grid killed stopping rewards are integrable, including the BV origin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q x : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation) (hx : 0 ≤ x)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (hclock0 : clock 0 = 0)
    (lower upper : ℝ) (m : ℕ) :
    Integrable (fun ω =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ clock (hittingBtwn
          (fun k ξ => max (X.X (clock k) ξ - upper)
            (lower - X.X (clock k) ξ))
          (Set.Ioi (0 : ℝ)) 0 m η) →
            0 ≤ x + X.X s η}).indicator
        (fun η =>
          Real.exp (-(q * (clock (hittingBtwn
            (fun k ξ => max (X.X (clock k) ξ - upper)
              (lower - X.X (clock k) ξ))
            (Set.Ioi (0 : ℝ)) 0 m η) : ℝ))) *
          W (x + X.X (clock (hittingBtwn
            (fun k ξ => max (X.X (clock k) ξ - upper)
              (lower - X.X (clock k) ξ))
            (Set.Ioi (0 : ℝ)) 0 m η)) η)) ω) P := by
  let Y : Ω → ℝ := fun ω =>
    ({η : Ω | ∀ s : ℝ≥0,
      s ≤ clock (hittingBtwn
        (fun k ξ => max (X.X (clock k) ξ - upper)
          (lower - X.X (clock k) ξ))
        (Set.Ioi (0 : ℝ)) 0 m η) → 0 ≤ x + X.X s η}).indicator
      (fun η => Real.exp (-(q * (clock (hittingBtwn
        (fun k ξ => max (X.X (clock k) ξ - upper)
          (lower - X.X (clock k) ξ))
        (Set.Ioi (0 : ℝ)) 0 m η) : ℝ))) *
        W (x + X.X (clock (hittingBtwn
          (fun k ξ => max (X.X (clock k) ξ - upper)
            (lower - X.X (clock k) ξ))
          (Set.Ioi (0 : ℝ)) 0 m η)) η)) ω
  change Integrable Y P
  have hWpos : 0 < W x := by
    rcases eq_or_lt_of_le hx with hZero | hPos
    · have hxZero : x = 0 := hZero.symm
      subst x
      rw [bv_scale_origin_eq_inv_drift X hX q hq W hW hBV]
      exact one_div_pos.mpr (bv_standing_drift_pos X hX hBV).1
    · exact scaleFunction_strict_pos_of_standing X hX q hq W hW x hPos
  have hE : (∫ ω, Y ω ∂P) = W x := by
    simpa only [Y] using
      (avram_ws01b_bv_killed_scale_grid_optional_stopping
        X hX q x hq W hW hBV hx clock hc hclock0 lower upper m)
  by_contra hn
  have hzero : (∫ ω, Y ω ∂P) = 0 := integral_undef hn
  rw [hE] at hzero
  exact (ne_of_gt hWpos) hzero
