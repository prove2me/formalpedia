-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.mFourierCoefficient_coverRepresentative_eq_twistedAverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/71eac90c-f33d-48f6-a73e-e52cdd50634d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularBoxMeasure_eq_restrict
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_coverRepresentative_coe
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_fourier_times_cover_eq_radial_twist
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_measurableSet_angularBox
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularBox_eq_setOf

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
theorem _root_.solution
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) (x : Space n) :
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m =
      WeightedTorusHilbert.radialCharacter m x *
        twistedAngularAverage F m x := by
  calc
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m =
      ∫ t : Space n in angularBox n,
        UnitAddTorus.mFourier (-m)
          (fun i => (t i : UnitAddCircle)) *
            coverRepresentative F x
              (fun i => (t i : UnitAddCircle)) := by
          simpa [angularBox_eq_setOf, smul_eq_mul] using
            UnitAddTorus.mFourierCoeff_eq_integral
              (coverRepresentative F x) m (fun _ => 0)
    _ = ∫ t : Space n,
        (WeightedTorusHilbert.radialCharacter m x *
          twistedAngularIntegrand F m x t)
          ∂(angularBoxMeasure n) := by
          rw [angularBoxMeasure_eq_restrict]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem
            (measurableSet_angularBox n)] with t ht
          rw [coverRepresentative_coe F x t ht]
          exact fourier_times_cover_eq_radial_twist F m x t
    _ = WeightedTorusHilbert.radialCharacter m x *
        twistedAngularAverage F m x := by
          exact MeasureTheory.integral_const_mul _ _
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
