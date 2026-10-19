-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.periodic_globalLaurentTwist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/3ededcb3-15f6-44f4-b100-f007b2a68616

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
    {F : TorusCharacters.LogSpace n → ℂ}
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m q : Fin n → ℤ) :
    Function.Periodic (globalLaurentTwist F m)
      (TorusCharacters.imaginaryShift q) := by
  intro ζ
  unfold globalLaurentTwist
  rw [TorusCharacters.characterExponent_add,
    TorusCharacters.characterExponent_imaginaryShift,
    neg_add_rev, Complex.exp_add, hperiod q ζ]
  have hneg :
      -(((∑ i, m i * q i : ℤ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I)) =
        ((-(∑ i, m i * q i : ℤ) : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hneg, Complex.exp_int_mul_two_pi_mul_I]
  ring
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
