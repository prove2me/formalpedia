-- Prove2me | solution 1 for ConvexAnalysis.local_max_second_derivative_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:24.00673+00:00
-- url     : https://prove2.me/submissions/80c6616d-680d-42b1-90b3-0da3521c85a5

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Theorems.Thm_ConvexAnalysis_convex_frontier_radial_derivative_ne_zero
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open BirkhoffGlobalSection ConvexAnalysis Filter Set
open scoped ContDiff Topology


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (f : ℝ → ℝ) (x : ℝ)
    (hmax : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp hmax.deriv_eq_zero hc
  have heq : f =ᶠ[nhds x] (fun _ => f x) := by
    filter_upwards [hmax, hmin] with t htmax htmin
    exact le_antisymm htmax htmin
  have hz : deriv (deriv f) x = 0 := by simpa using heq.deriv.deriv_eq
  linarith
