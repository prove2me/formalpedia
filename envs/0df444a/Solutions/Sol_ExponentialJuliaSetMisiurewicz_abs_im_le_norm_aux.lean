-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.abs_im_le_norm_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:05.99085+00:00
-- url     : https://prove2.me/submissions/7b0dae8b-d127-48a0-b08e-63dd25ecb7bd

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution (w : ℂ) :
    |w.im| ≤ ‖w‖ := by
  exact Complex.abs_im_le_norm w
end ExponentialJuliaSetMisiurewicz
