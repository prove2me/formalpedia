-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularCharacter_mul_slice_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/1f61c779-bae3-44de-87c1-d6e30496f30f

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
    {g : TorusCharacters.AngularTorus n → ℂ}
    (hg : MemLp g 2
      (WeightedTorusHilbert.angularMeasure n))
    (m : Fin n → ℤ) :
    Integrable
      (fun θ : TorusCharacters.AngularTorus n =>
        UnitAddTorus.mFourier (-m) θ * g θ)
      (WeightedTorusHilbert.angularMeasure n) := by
  refine (hg.integrable (by norm_num)).bdd_mul (c := (1 : ℝ))
    (UnitAddTorus.mFourier (-m)).continuous.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun θ => by
    rw [WeightedTorusHilbert.angularCharacter_norm]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
