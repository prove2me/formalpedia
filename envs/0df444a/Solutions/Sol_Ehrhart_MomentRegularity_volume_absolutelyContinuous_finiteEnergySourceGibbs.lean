-- Prove2me | solution 1 for Ehrhart.MomentRegularity.volume_absolutelyContinuous_finiteEnergySourceGibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/6d6d4ec7-aab1-4594-a0f6-70526854aa3f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MomentRegularity
open Set Function Filter MeasureTheory
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open scoped ENNReal Topology
namespace Ehrhart.MomentRegularity
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    (volume : Measure (Space n)) ≪
      finiteEnergySourceGibbsProbability F := by
  change
    (volume : Measure (Space n)) ≪
      (volume : Measure (Space n)).withDensity
        (fun x => ENNReal.ofReal
          (WeightedPoincare.normalizedDensity
            F.potential x))
  apply MeasureTheory.withDensity_absolutelyContinuous'
  · exact
      ((Real.continuous_exp.comp F.potential.continuous.neg).div_const
        (WeightedPoincare.partition F.potential)).measurable
          |>.ennreal_ofReal.aemeasurable
  · filter_upwards with x
    exact
      (ENNReal.ofReal_pos.mpr
        (WeightedPoincare.normalizedDensity_pos
          F.densityIntegrable x)).ne'
end Ehrhart.MomentRegularity
