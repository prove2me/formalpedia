-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.differentiableOn_cayleyUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:33.954306+00:00
-- url     : https://prove2.me/submissions/03de32eb-9f75-4133-9d5f-a6e66c93cc9c

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_add_I_ne_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiable_expIterate


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {U : Set ℂ} {n : ℕ}
    (hpos : ∀ z ∈ U, 0 < (expIterate n z).im) :
    DifferentiableOn ℂ
      (fun w => (expIterate n w - Complex.I) / (expIterate n w + Complex.I)) U := by
  intro z hz
  have h1 : DifferentiableAt ℂ (expIterate n) z := differentiable_expIterate n z
  exact (((h1.sub_const _).div (h1.add_const _)
    (add_I_ne_zero (hpos z hz)))).differentiableWithinAt
end ExponentialJuliaSetMisiurewicz
