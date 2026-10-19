-- Prove2me | solution 1 for Ehrhart.BergmanJetDualPhaseConcentration.momentNormalized_phaseMaximizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/2f721281-113f-4cd9-bea9-c09e3b8bb89c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetDualPhaseConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentInteriorLegendre
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetDualPhaseConcentration
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (u x : Space n) :
    (∀ z : Space n,
      phase u (momentNormalizedPotential F) z ≤
        phase u (momentNormalizedPotential F) x) ↔
    (∀ z : Space n,
      phase u F.potential z ≤ phase u F.potential x) := by
  constructor <;> intro h z
  · have hz := h z
    simp only [phase, momentNormalizedPotential] at hz ⊢
    linarith
  · have hz := h z
    simp only [phase, momentNormalizedPotential] at hz ⊢
    linarith
end Ehrhart.BergmanJetDualPhaseConcentration
