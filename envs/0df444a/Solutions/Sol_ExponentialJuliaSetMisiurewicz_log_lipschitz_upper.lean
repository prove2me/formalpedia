-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.log_lipschitz_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:06.78701+00:00
-- url     : https://prove2.me/submissions/0d246b42-b072-42a0-9d33-a113449210f1

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Periodic

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution :
    LipschitzOnWith 1 Complex.log {z : ℂ | 1 ≤ z.im} := by
  apply (convex_halfSpace_im_ge 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z hz => (Complex.hasDerivAt_log (Or.inr (by
      have hz' : 1 ≤ z.im := hz
      linarith : z.im ≠ 0))).hasDerivWithinAt)
  intro z hz
  change ‖z⁻¹‖ ≤ (1 : ℝ)
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ (hz.trans (Complex.im_le_norm z))
end ExponentialJuliaSetMisiurewicz
