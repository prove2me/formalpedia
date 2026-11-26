-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma3_isOpen_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:33.800216+00:00
-- url     : https://prove2.me/submissions/9c5e9c82-eca1-4743-926e-6cf7ee81210b

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_image_of_injOn

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {g : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hg : DifferentiableOn ℂ g (ball b r))
    (hinj : Set.InjOn g (ball b r)) :
    IsOpen (g '' ball b r) :=
  isOpen_image_of_injOn isOpen_ball hg hinj
end ExponentialJuliaSetMisiurewicz
