-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.continuous_twistedAngularIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/67d62514-476e-409f-9a71-b20486d08ebd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_differentiable_globalLaurentTwist

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
    (hF : Differentiable ℂ F) (m : Fin n → ℤ)
    (x : Space n) :
    Continuous (twistedAngularIntegrand F m x) := by
  unfold twistedAngularIntegrand logarithmicPoint
  apply (differentiable_globalLaurentTwist hF m).continuous.comp
  fun_prop
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
