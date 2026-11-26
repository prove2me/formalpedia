-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.dense_repelling_periodic_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:17:48.026617+00:00
-- url     : https://prove2.me/submissions/bad4609a-4140-417e-b820-db9fe0f9e9ae

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_repelling_periodic_mem_open

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution :
    Dense {p : ℂ | ∃ n : ℕ,
      0 < n ∧ expIterate n p = p ∧ 1 < ‖deriv (expIterate n) p‖} := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨p, hp, hperiod⟩ := exists_repelling_periodic_mem_open hU hUne
  exact ⟨p, hp, hperiod⟩
end ExponentialJuliaSetMisiurewicz
