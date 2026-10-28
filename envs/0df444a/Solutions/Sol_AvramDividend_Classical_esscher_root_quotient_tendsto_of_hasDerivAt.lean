-- Prove2me | solution 1 for AvramDividend.Classical.esscher_root_quotient_tendsto_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:44:22.587282+00:00
-- url     : https://prove2.me/submissions/373e0eff-c9a8-4c19-b6a4-7bf7d3a0d56e

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set

/-- Positive roots approaching zero inherit the right-hand secant slope. -/
theorem solution
    (g root : ℝ → ℝ) (m : ℝ)
    (hzero : g 0 = 0)
    (hm : 0 < m)
    (hderiv : HasDerivAt g m 0)
    (hrootTendsto : Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hroot : ∀ p : ℝ, 0 < p → g (root p) = p) :
    Tendsto (fun p : ℝ => p / root p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) := by
  have hquot :
      Tendsto (fun p : ℝ => (root p)⁻¹ • (g (0 + root p) - g 0))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) :=
    hderiv.tendsto_slope_zero_right.comp hrootTendsto
  have heq :
      (fun p : ℝ => p / root p) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
        (fun p : ℝ => (root p)⁻¹ • (g (0 + root p) - g 0)) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp_pos : 0 < p := hp
    dsimp
    rw [zero_add, hzero, sub_zero, hroot p hp_pos]
    ring
  exact hquot.congr' heq.symm
