-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.twistedAngularIntegral_coordinate_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/0b187003-7889-45d5-b885-fe6dd664d233

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_continuous_twistedAngularIntegrand
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_coordinate_unit_interval_twist_integral_eq
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularBoxIntegral_eq_of_coordinate_slice
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_logarithmicPoint_insertNth
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_logarithmicPoint_update_insertNth

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
    (m : Fin n → ℤ) (x : Space n)
    (i : Fin n) (a : ℝ) :
    (∫ t : Space n,
      twistedAngularIntegrand F m x t
        ∂(angularBoxMeasure n)) =
      ∫ t : Space n,
        twistedAngularIntegrand F m
          (Function.update x i a) t
          ∂(angularBoxMeasure n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    apply angularBoxIntegral_eq_of_coordinate_slice
      (continuous_twistedAngularIntegrand hF m x)
      (continuous_twistedAngularIntegrand hF m
        (Function.update x i a)) i
    intro y
    have h :=
      coordinate_unit_interval_twist_integral_eq
        hF hperiod m
        (logarithmicPoint x (i.insertNth 0 y)) i
        (a / 2) (x i / 2)
    calc
      (∫ t : ℝ in 0..1,
        twistedAngularIntegrand F m x (i.insertNth t y)) =
        ∫ t : ℝ in 0..1,
          globalLaurentTwist F m
            (fun j => if j = i
              then ((x i / 2 : ℝ) : ℂ) +
                (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
              else logarithmicPoint x (i.insertNth 0 y) j) := by
            apply intervalIntegral.integral_congr
            intro t ht
            unfold twistedAngularIntegrand
            apply congrArg (globalLaurentTwist F m)
            simpa only [Complex.ofReal_div,
              Complex.ofReal_ofNat] using
              logarithmicPoint_insertNth x i y t
      _ = ∫ t : ℝ in 0..1,
          globalLaurentTwist F m
            (fun j => if j = i
              then ((a / 2 : ℝ) : ℂ) +
                (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
              else logarithmicPoint x (i.insertNth 0 y) j) := h
      _ = ∫ t : ℝ in 0..1,
          twistedAngularIntegrand F m
            (Function.update x i a) (i.insertNth t y) := by
            apply intervalIntegral.integral_congr
            intro t ht
            unfold twistedAngularIntegrand
            apply congrArg (globalLaurentTwist F m)
            symm
            simpa only [Complex.ofReal_div,
              Complex.ofReal_ofNat] using
              logarithmicPoint_update_insertNth x i a y t
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
