-- Prove2me | solution 1 for Ehrhart.BergmanJetBergmanProbabilityTransfer.momentWeakTorusGibbsProbability_eq_base_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/b45e411f-eed6-45c4-bf03-ae8c229bda4b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetBergmanProbabilityTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanMonomials BergmanNormalization
open JetEnvelopeSlopeConvergence LogPartitionConvexity MomentOptimizer MomentWeakFirstVariation
open MomentRegularity MomentWeakBergman MomentWeakBergmanProbabilityEndpoint
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetBergmanProbabilityTransfer
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    momentWeakTorusGibbsProbability F =
      (sourceTorusBaseMeasure n).withDensity
        (fun q : LogTorus n =>
          ENNReal.ofReal (momentWeakTorusGibbsDensity F q)) := by
  have hmeas : Measurable
      (fun x : Space n => ENNReal.ofReal
        (WeightedPoincare.normalizedDensity F.potential x)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp F.potential.continuous.neg).div_const
        (WeightedPoincare.partition F.potential)).measurable
  unfold momentWeakTorusGibbsProbability
    finiteEnergySourceGibbsProbability
    WeightedPoincare.normalizedMeasure
    sourceTorusBaseMeasure momentWeakTorusGibbsDensity
  exact MeasureTheory.prod_withDensity_left hmeas
end Ehrhart.BergmanJetBergmanProbabilityTransfer
