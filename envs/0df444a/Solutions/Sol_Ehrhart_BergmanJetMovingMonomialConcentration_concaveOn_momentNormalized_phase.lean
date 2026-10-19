-- Prove2me | solution 1 for Ehrhart.BergmanJetMovingMonomialConcentration.concaveOn_momentNormalized_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/9784a7ef-272b-447a-92a2-531982bc2f12

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentWeakBergman_convexOn_momentNormalizedPotential

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetMovingMonomialConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentWeakBergman BergmanJetMovingPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetMovingMonomialConcentration
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (u : Space n) :
    ConcaveOn ℝ Set.univ
      (phase u (momentNormalizedPotential F)) := by
  have hlinear :
      ConcaveOn ℝ Set.univ
        (BergmanAsymptotics.pairingLinear u) :=
    (BergmanAsymptotics.pairingLinear u).concaveOn convex_univ
  have hphase :
      (BergmanAsymptotics.pairingLinear u :
        Space n → ℝ) -
          momentNormalizedPotential F =
        phase u (momentNormalizedPotential F) := by
    funext x
    rfl
  rw [← hphase]
  exact hlinear.sub (convexOn_momentNormalizedPotential F)
end Ehrhart.BergmanJetMovingMonomialConcentration
