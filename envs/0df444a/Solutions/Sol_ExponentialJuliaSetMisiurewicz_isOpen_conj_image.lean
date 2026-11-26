-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.isOpen_conj_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:38.244235+00:00
-- url     : https://prove2.me/submissions/0998597a-3bb3-47d2-bfc6-44c6e3afd1e1

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_conj_image_eq_preimage

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {V : Set ℂ} (hV : IsOpen V) :
    IsOpen ((starRingEnd ℂ) '' V) := by
  rw [conj_image_eq_preimage]
  exact hV.preimage Complex.continuous_conj
end ExponentialJuliaSetMisiurewicz
