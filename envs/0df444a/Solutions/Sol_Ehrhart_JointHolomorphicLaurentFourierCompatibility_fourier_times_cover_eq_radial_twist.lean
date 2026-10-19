-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.fourier_times_cover_eq_radial_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/f69a4518-748a-4cd5-90c4-a718f282efb2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) (x t : Space n) :
    UnitAddTorus.mFourier (-m)
        (fun i => (t i : UnitAddCircle)) *
          F (logarithmicPoint x t) =
      WeightedTorusHilbert.radialCharacter m x *
        twistedAngularIntegrand F m x t := by
  rw [mFourier_neg_coe_eq_exp]
  unfold WeightedTorusHilbert.radialCharacter
    TorusCharacters.torusCharacter
    twistedAngularIntegrand globalLaurentTwist
  rw [characterExponent_logarithmicPoint m x t]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  ring
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
