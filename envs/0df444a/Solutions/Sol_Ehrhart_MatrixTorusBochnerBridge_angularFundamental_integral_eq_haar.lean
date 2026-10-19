-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.angularFundamental_integral_eq_haar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/6fd45253-286a-48ca-abf1-4cb7ad7ca631

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ}
    {g : TorusCharacters.AngularTorus n → ℂ}
    (hg : Continuous g) :
    (∫ t : Space n
      in angularFundamentalBox (0 : Space n),
      g (angularCoverProjection n t)
      ∂(volume : Measure (Space n))) =
      ∫ θ : TorusCharacters.AngularTorus n,
        g θ ∂(angularMeasure n) := by
  let μ : Measure (Space n) :=
    (volume : Measure (Space n)).restrict
      (angularFundamentalBox (0 : Space n))
  have hp :=
    angularCoverProjection_measurePreserving (0 : Space n)
  change
    (∫ t : Space n,
      g (angularCoverProjection n t) ∂μ) = _
  calc
    _ = ∫ θ : TorusCharacters.AngularTorus n,
      g θ ∂(Measure.map (angularCoverProjection n) μ) := by
      exact (MeasureTheory.integral_map
        hp.measurable.aemeasurable
        hg.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]
end Ehrhart.MatrixTorusBochnerBridge
