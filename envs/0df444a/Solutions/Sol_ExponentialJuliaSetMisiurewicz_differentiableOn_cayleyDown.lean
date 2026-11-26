-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.differentiableOn_cayleyDown
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:52.058875+00:00
-- url     : https://prove2.me/submissions/96974944-e0dd-4f9e-8562-351acd904ea0

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_sub_I_ne_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiable_expIterate


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {U : Set ℂ} {n : ℕ}
    (hneg : ∀ z ∈ U, (expIterate n z).im < 0) :
    DifferentiableOn ℂ
      (fun w => (expIterate n w + Complex.I) / (expIterate n w - Complex.I)) U := by
  intro z hz
  have h1 : DifferentiableAt ℂ (expIterate n) z := differentiable_expIterate n z
  exact (((h1.add_const _).div (h1.sub_const _)
    (sub_I_ne_zero (hneg z hz)))).differentiableWithinAt
end ExponentialJuliaSetMisiurewicz
