-- Prove2me | solution 1 for Ehrhart.MomentWeakBergmanProbabilityEndpoint.normalizedMonomialDensity_momentNormalized_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/79e549ce-ad1d-4838-a2ac-525b452d803b

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
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) (x : Space n) :
    0 < normalizedMonomialDensity
      K k (momentNormalizedPotential F) u x := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  unfold normalizedMonomialDensity
  apply div_pos
  · exact Real.exp_pos _
  · exact monomialIntegral_momentNormalized_pos
      F htransport u.property.1 hkreal
end Ehrhart.MomentWeakBergmanProbabilityEndpoint
