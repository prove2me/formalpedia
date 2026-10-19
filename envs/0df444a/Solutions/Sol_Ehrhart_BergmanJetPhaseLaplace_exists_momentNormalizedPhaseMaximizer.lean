-- Prove2me | solution 1 for Ehrhart.BergmanJetPhaseLaplace.exists_momentNormalizedPhaseMaximizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/a01b19f3-8250-48d4-b95a-ee7a101d0254

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPhaseLaplace
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetPhaseLaplace
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∃ x : Space n, ∀ y : Space n,
      phase u (momentNormalizedPotential F) y ≤
        phase u (momentNormalizedPotential F) x := by
  obtain ⟨δ, C, hδ, hcoerc⟩ :=
    exists_momentNormalized_phase_linear_coercivity
      F htransport hu
  let φ := momentNormalizedPotential F
  let R : ℝ := max 0 ((C - phase u φ 0) / δ)
  apply (continuous_phase u
    (continuous_momentNormalizedPotential F)).exists_forall_ge' 0
  filter_upwards [
    (isCompact_closedBall (0 : Space n) R).compl_mem_cocompact
  ] with x hx
  have hxnorm : R < ‖x‖ := by
    apply lt_of_not_ge
    intro h
    apply hx
    simpa [Metric.mem_closedBall] using h
  have hR : C - phase u φ 0 ≤ δ * R := by
    have hrange : (C - phase u φ 0) / δ ≤ R :=
      le_max_right _ _
    simpa [mul_comm] using (div_le_iff₀ hδ).mp hrange
  have hscale := mul_lt_mul_of_pos_left hxnorm hδ
  have hbound := hcoerc x
  change phase u φ x ≤ phase u φ 0
  change phase u φ x ≤ C - δ * ‖x‖ at hbound
  nlinarith
end Ehrhart.BergmanJetPhaseLaplace
