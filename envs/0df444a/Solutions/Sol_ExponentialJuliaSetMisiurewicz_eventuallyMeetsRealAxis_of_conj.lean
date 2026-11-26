-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.eventuallyMeetsRealAxis_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:59.508929+00:00
-- url     : https://prove2.me/submissions/a0551e52-d2a5-427e-aaa8-b914bdaaad8c

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_conj

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {V : Set ℂ}
    (h : EventuallyMeetsRealAxis ((starRingEnd ℂ) '' V)) :
    EventuallyMeetsRealAxis V := by
  obtain ⟨n, z, hz, hval⟩ := h
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨n, y, hy, ?_⟩
  rw [expIterate_conj] at hval
  show (expIterate n y).im = 0
  have : -(expIterate n y).im = 0 := hval
  linarith
end ExponentialJuliaSetMisiurewicz
