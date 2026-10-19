-- Prove2me | solution 1 for Ehrhart.MomentWeakBergmanProbabilityEndpoint.momentNormalizedDensity_div_volume_eq_gibbsDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/b665675b-3faf-4e60-b8c4-9f436665256c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MomentWeakBergmanProbabilityEndpoint
open Set Function Filter MeasureTheory
open BergmanMonomials BergmanNormalization LatticeAsymptotics MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman MomentWeakGlobalKernel
open scoped BigOperators ENNReal Topology
namespace Ehrhart.MomentWeakBergmanProbabilityEndpoint
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) (x : Space n) :
    Real.exp (-momentNormalizedPotential F x) /
        normalizedVolume K.carrier =
      WeightedPoincare.normalizedDensity F.potential x := by
  rw [exp_neg_momentNormalizedPotential F x]
  change
    (normalizedVolume K.carrier /
      finiteEnergySourcePartition F * Real.exp (-F.potential x)) /
      normalizedVolume K.carrier =
        Real.exp (-F.potential x) /
          finiteEnergySourcePartition F
  field_simp [K.volume_pos.ne',
    (finiteEnergySourcePartition_pos F).ne']
end Ehrhart.MomentWeakBergmanProbabilityEndpoint
