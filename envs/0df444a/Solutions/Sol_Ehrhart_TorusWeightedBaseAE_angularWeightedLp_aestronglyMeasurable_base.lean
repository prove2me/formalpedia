-- Prove2me | solution 1 for Ehrhart.TorusWeightedBaseAE.angularWeightedLp_aestronglyMeasurable_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/0db9be0c-19ba-4cae-ba77-aff43440aa2e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedBaseAE
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology ContDiff
namespace Ehrhart.TorusWeightedBaseAE
theorem _root_.solution
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E]
    {a : LogTorus n → ℝ}
    (f : MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a)) :
    AEStronglyMeasurable
      (fun p : LogTorus n => f p)
      (sourceTorusBaseMeasure n) := by
  exact (MeasureTheory.Lp.stronglyMeasurable f).aestronglyMeasurable
end Ehrhart.TorusWeightedBaseAE
