-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.dense_periodicPts_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:19:19.992386+00:00
-- url     : https://prove2.me/submissions/187871e9-7a75-4cf5-8211-0e2061315be8

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_periodic_points

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution : Dense (Function.periodicPts Complex.exp) := by
  apply dense_periodic_points.mono
  rintro p ⟨n, hn, hp⟩
  exact Function.mk_mem_periodicPts hn hp
end ExponentialJuliaSetMisiurewicz
