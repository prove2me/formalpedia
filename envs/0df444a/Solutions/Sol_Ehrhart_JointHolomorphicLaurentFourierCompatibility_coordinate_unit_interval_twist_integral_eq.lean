-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.coordinate_unit_interval_twist_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/e1e0ebe9-e96c-4ec8-9ac3-e0f7fe38eec6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_differentiable_coordinateHolomorphicSlice
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_periodic_coordinateHolomorphicSlice
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_differentiable_globalLaurentTwist
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_periodic_globalLaurentTwist
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_unit_interval_vertical_integral_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918
namespace Ehrhart.JointHolomorphicLaurentFourierCompatibility
theorem _root_.solution {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ)
    (ζ : TorusCharacters.LogSpace n)
    (i : Fin n) (a b : ℝ) :
    (∫ t : ℝ in 0..1,
      globalLaurentTwist F m
        (fun j => if j = i
          then (b : ℂ) +
            (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
          else ζ j)) =
      ∫ t : ℝ in 0..1,
        globalLaurentTwist F m
          (fun j => if j = i
            then (a : ℂ) +
              (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
            else ζ j) := by
  apply unit_interval_vertical_integral_eq
    (HolomorphicLaurentFourierCompletenessBridge.differentiable_coordinateHolomorphicSlice
      (differentiable_globalLaurentTwist hF m) ζ i)
    (HolomorphicLaurentFourierCompletenessBridge.periodic_coordinateHolomorphicSlice
      (fun q => periodic_globalLaurentTwist hperiod m q) ζ i)
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
