-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.torusMonomial_angular_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/857f36af-20f0-451f-9699-a31993c46d04

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
    (m : Fin n → ℤ) (x : Space n) :
    MemLp
      (fun θ : TorusCharacters.AngularTorus n =>
        WeightedTorusHilbert.torusMonomial m (x, θ))
      2 (WeightedTorusHilbert.angularMeasure n) := by
  refine MeasureTheory.MemLp.of_bound
    ((WeightedTorusHilbert.continuous_torusMonomial m).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    ‖WeightedTorusHilbert.radialCharacter m x‖ ?_
  exact Filter.Eventually.of_forall fun θ => by
    simp [WeightedTorusHilbert.torusMonomial,
      WeightedTorusHilbert.angularCharacter_norm]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
