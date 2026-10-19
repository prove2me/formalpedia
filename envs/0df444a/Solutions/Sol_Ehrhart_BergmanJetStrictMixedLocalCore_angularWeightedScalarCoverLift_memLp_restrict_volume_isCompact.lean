-- Prove2me | solution 1 for Ehrhart.BergmanJetStrictMixedLocalCore.angularWeightedScalarCoverLift_memLp_restrict_volume_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/5548e45d-e00a-4c79-b1be-653165e34d62

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetStrictMixedLocalCore_angularMemLp_normSquared_locallyIntegrable_base

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetStrictMixedLocalCore
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusVectorClosedGraphWeakBridge WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetStrictMixedLocalCore
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    {S : Set (LogSpace n)} (hS : IsCompact S) :
    MemLp
      (complexTorusCoverLift
        (fun q : LogTorus n => f q))
      2 ((volume : Measure (LogSpace n)).restrict S) := by
  have hmeas :
      AEStronglyMeasurable
        (complexTorusCoverLift
          (fun q : LogTorus n => f q))
        ((volume : Measure (LogSpace n)).restrict S) :=
    (angularWeightedScalarCoverLift_locallyIntegrable
      ha f).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hbase :=
    angularMemLp_normSquared_locallyIntegrable_base
      ha (MeasureTheory.Lp.memLp f)
  have hcover :=
    complexTorusCoverLift_locallyIntegrable
      (show
        LocallyIntegrable
          (fun q : LogTorus n => ((‖f q‖ ^ 2 : ℝ) : ℂ))
          (unweightedTorusMeasure n) by
        simpa [unweightedTorusMeasure, sourceTorusBaseMeasure]
          using hbase)
  have hsq := (hcover.integrableOn_isCompact hS).re
  apply hsq.congr
  filter_upwards [] with z
  change
    (((‖f (complexTorusCoverProjection n z)‖ ^ 2 : ℝ) : ℂ)).re =
      ‖f (complexTorusCoverProjection n z)‖ ^ 2
  exact Complex.ofReal_re _
end Ehrhart.BergmanJetStrictMixedLocalCore
