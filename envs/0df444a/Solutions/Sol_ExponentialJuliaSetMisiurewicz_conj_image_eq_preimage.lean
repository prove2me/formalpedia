-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.conj_image_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:50.029805+00:00
-- url     : https://prove2.me/submissions/258f6980-ff0e-4bcc-958b-847739ec08a4

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution (V : Set ℂ) :
    (starRingEnd ℂ) '' V = (starRingEnd ℂ) ⁻¹' V := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hz
    exact ⟨(starRingEnd ℂ) z, hz, by simp⟩
end ExponentialJuliaSetMisiurewicz
