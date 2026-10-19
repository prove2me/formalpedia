-- Prove2me | solution 1 for Ehrhart.BergmanJetJointHolomorphicApproximation.integrable_momentWeakHolomorphicJointRadialEnvelopeCircleIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/f232946f-22fc-466f-9966-48774ef7a3b8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetJointHolomorphicApproximation
open Set Function Filter MeasureTheory Metric
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicClosure BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialMollifier
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
attribute [local instance] Ehrhart.BergmanJetJointHolomorphicApproximation.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.BergmanJetJointHolomorphicApproximation
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : SourceJointComplexCover n) :
    Integrable
      (fun z : SourceJointComplexCover n × ℝ =>
        sourceJointTrueRadialMollifier n k z.1 *
          momentWeakJointCoverUpperEnvelope K F htransport p
            (q - circleMap 0 1 z.2 • z.1))
      ((volume : Measure (SourceJointComplexCover n)).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall q (1 : ℝ)).image
      (continuous_momentWeakHolomorphicJointAbsoluteMajorant K F)).bddAbove
  have hCnonneg : 0 ≤ C := by
    have hq : q ∈ Metric.closedBall q (1 : ℝ) := by simp
    have hmaj : momentWeakHolomorphicJointAbsoluteMajorant K F q ≤ C :=
      hC ⟨q, hq, rfl⟩
    exact (norm_nonneg
      (momentWeakJointCoverUpperEnvelope K F htransport p q)).trans
      ((norm_momentWeakJointCoverUpperEnvelope_le_majorant
        K F htransport p q).trans hmaj)
  have hdom :
      Integrable
        (fun z : SourceJointComplexCover n × ℝ =>
          sourceJointTrueRadialMollifier n k z.1 * C)
        ((volume : Measure (SourceJointComplexCover n)).prod ν) := by
    exact (integrable_sourceJointTrueRadialMollifier n k).mul_prod
      (integrable_const C)
  have hmap : Continuous
      (fun z : SourceJointComplexCover n × ℝ =>
        q - circleMap 0 1 z.2 • z.1) := by
    fun_prop
  have hmeas : Measurable
      (fun z : SourceJointComplexCover n × ℝ =>
        sourceJointTrueRadialMollifier n k z.1 *
          momentWeakJointCoverUpperEnvelope K F htransport p
            (q - circleMap 0 1 z.2 • z.1)) :=
    ((contDiff_sourceJointTrueRadialMollifier n k).continuous.measurable.comp
      measurable_fst).mul
        ((measurable_momentWeakJointCoverUpperEnvelope
          K F htransport p).comp hmap.measurable)
  change Integrable _ ((volume : Measure
    (SourceJointComplexCover n)).prod ν)
  apply hdom.mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : sourceJointTrueRadialMollifier n k z.1 = 0
    · simp [hz]
    · have hsupp :=
        support_sourceJointTrueRadialMollifier_subset_closedBall k hz
      have hnorm : ‖z.1‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hsupp
      have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_lt_succ k
      have hradius : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
        apply (div_le_iff₀ hk).mpr
        norm_num
      have hpoint :
          q - circleMap 0 1 z.2 • z.1 ∈
            Metric.closedBall q (1 : ℝ) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hunit : ‖circleMap 0 1 z.2‖ = 1 := by
          simp [norm_circleMap_zero]
        simpa [sub_eq_add_neg, norm_smul, hunit,
          add_assoc, add_left_comm, add_comm] using
          hnorm.trans hradius
      have hmaj :
          momentWeakHolomorphicJointAbsoluteMajorant K F
            (q - circleMap 0 1 z.2 • z.1) ≤ C :=
        hC ⟨_, hpoint, rfl⟩
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (sourceJointTrueRadialMollifier_nonneg n k z.1)]
      exact mul_le_mul_of_nonneg_left
        ((norm_momentWeakJointCoverUpperEnvelope_le_majorant
          K F htransport p _).trans hmaj)
        (sourceJointTrueRadialMollifier_nonneg n k z.1)
end Ehrhart.BergmanJetJointHolomorphicApproximation
