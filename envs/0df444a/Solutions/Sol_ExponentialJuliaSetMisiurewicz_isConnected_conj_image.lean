-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.isConnected_conj_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:58.74605+00:00
-- url     : https://prove2.me/submissions/104f71da-2725-4b12-96bc-bec540f60029

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {V : Set ℂ} (hV : IsConnected V) :
    IsConnected ((starRingEnd ℂ) '' V) :=
  hV.image _ Complex.continuous_conj.continuousOn
end ExponentialJuliaSetMisiurewicz
