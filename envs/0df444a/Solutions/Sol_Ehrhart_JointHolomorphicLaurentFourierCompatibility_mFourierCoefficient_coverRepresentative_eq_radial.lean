-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.mFourierCoefficient_coverRepresentative_eq_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/6170fdbf-9a9d-4d57-a79d-5c9fb88c3b85

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_twistedAngularAverage_eq_zero
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_mFourierCoefficient_coverRepresentative_eq_twistedAverage

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
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ) (x : Space n) :
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m =
      UnitAddTorus.mFourierCoeff
          (coverRepresentative F 0) m *
        WeightedTorusHilbert.radialCharacter m x := by
  have hzero :
      UnitAddTorus.mFourierCoeff
          (coverRepresentative F 0) m =
        twistedAngularAverage F m 0 := by
    rw [mFourierCoefficient_coverRepresentative_eq_twistedAverage]
    simp [WeightedTorusHilbert.radialCharacter,
      TorusCharacters.torusCharacter,
      TorusCharacters.characterExponent,
      TorusCharacters.realLogSlice]
  calc
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m =
      WeightedTorusHilbert.radialCharacter m x *
        twistedAngularAverage F m x :=
      mFourierCoefficient_coverRepresentative_eq_twistedAverage
        F m x
    _ = WeightedTorusHilbert.radialCharacter m x *
        twistedAngularAverage F m 0 := by
      rw [twistedAngularAverage_eq_zero hF hperiod]
    _ = UnitAddTorus.mFourierCoeff
          (coverRepresentative F 0) m *
        WeightedTorusHilbert.radialCharacter m x := by
      rw [hzero]
      ring
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
