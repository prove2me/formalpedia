-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.dense_periodic_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:18:32.60578+00:00
-- url     : https://prove2.me/submissions/5fe2d7a7-86c5-4028-adf8-ca7d7cd2c52d

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_repelling_periodic_points

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution :
    Dense {p : ℂ | ∃ n : ℕ, 0 < n ∧ expIterate n p = p} := by
  apply dense_repelling_periodic_points.mono
  rintro p ⟨n, hn, hperiod, _⟩
  exact ⟨n, hn, hperiod⟩
end ExponentialJuliaSetMisiurewicz
