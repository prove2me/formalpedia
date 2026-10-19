-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedTorusDescent.angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/b07ffb52-cbbb-4684-bbe7-07fe0d396a5e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_angularWeightedTorusDensity_pos
import Theorems.Thm_Ehrhart_TorusWeightedCoverAdjointGreen_ae_mem_angularFundamentalBox_realFundamentalCell
import Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_isCompact_sourceCompactAngularCoverBox
import Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_logarithmicPoint_mem_sourceCompactAngularCoverBox
import Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_torusScalarRepresentative_realTorusCoverProjection
import Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_angularWeightedTorus_integral_real_eq_realFundamentalCell
import Theorems.Thm_Ehrhart_TorusStrongWeightedTorusDescent_realFundamentalCell_integral_real_eq_coverJacobian

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongWeightedTorusDescent
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeightedCoverAdjointGreen
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongWeightedTorusDescent
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {f : LogTorus n → ℂ}
    (hfbase : AEStronglyMeasurable f (sourceTorusBaseMeasure n))
    (_ : LocallyIntegrable
      (complexTorusCoverLift f)
      (volume : Measure (LogSpace n)))
    (hflocal : ∀ {K : Set (LogSpace n)}, IsCompact K →
      MemLp (complexTorusCoverLift f) 2
        ((volume : Measure (LogSpace n)).restrict K))
    {F : ℕ → LogSpace n → ℂ}
    (hF : ∀ k : ℕ, Continuous (F k))
    (hFp : ∀ (k : ℕ) (d : Fin n → ℤ),
      Function.Periodic (F k) (imaginaryShift d))
    (hcover : ∀ {K : Set (LogSpace n)}, IsCompact K →
      Tendsto
        (fun k : ℕ =>
          ∫ z in K,
            ‖F k z - complexTorusCoverLift f z‖ ^ 2
              ∂(volume : Measure (LogSpace n)))
        atTop (nhds 0))
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun k : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative (F k) q - f q‖ ^ 2
            ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  classical
  let K : Set (LogSpace n) := sourceCompactAngularCoverBox S
  have hK : IsCompact K :=
    isCompact_sourceCompactAngularCoverBox hS
  obtain ⟨B₀, hB₀⟩ :=
    hS.bddAbove_image
      (continuous_angularWeightedTorusDensity ha).continuousOn
  let B : ℝ := max B₀ 0
  have hBpos : 0 ≤ B := le_max_right _ _
  have hB (q : LogTorus n) (hq : q ∈ S) :
      angularWeightedTorusDensity a q ≤ B :=
    (hB₀ ⟨q, hq, rfl⟩).trans (le_max_left _ _)
  let T : Set (LogSpace n) :=
    {z | ((logarithmicCoordinatesEquiv n).symm z).2 ∈
      angularFundamentalBox (0 : Space n)}
  let J : ℕ → LogSpace n → ℝ := fun k z =>
    T.indicator
      (((complexTorusCoverProjection n) ⁻¹' S).indicator
        (fun w : LogSpace n =>
          angularWeightedTorusDensity a
              (complexTorusCoverProjection n w) *
            ‖F k w - complexTorusCoverLift f w‖ ^ 2)) z
  have htorus (k : ℕ) :
      Continuous (torusScalarRepresentative (F k)) :=
    continuous_torusScalarRepresentative_of_periodic
      (hF k) (hFp k)
  have hbase (k : ℕ) :
      AEStronglyMeasurable
        (fun q : LogTorus n =>
          ‖torusScalarRepresentative (F k) q - f q‖ ^ 2)
        (sourceTorusBaseMeasure n) :=
    ((htorus k).aestronglyMeasurable.sub hfbase).norm.pow 2
  have hident (k : ℕ) :
      (∫ q in S,
        ‖torusScalarRepresentative (F k) q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n, J k z
          ∂(volume : Measure (LogSpace n))) := by
    rw [← MeasureTheory.integral_indicator hS.measurableSet]
    rw [angularWeightedTorus_integral_real_eq_realFundamentalCell
      ha (0 : Space n)
      ((hbase k).indicator hS.measurableSet)]
    rw [← realFundamentalCell_integral_real_eq_coverJacobian
      (0 : Space n) (J k)]
    · apply integral_congr_ae
      filter_upwards
        [ae_mem_angularFundamentalBox_realFundamentalCell
          (0 : Space n)] with p hp
      have hrep := torusScalarRepresentative_realTorusCoverProjection
        (F k) p hp
      have hT : (logarithmicCoordinatesEquiv n) p ∈ T := by
        change
          (((logarithmicCoordinatesEquiv n).symm
            ((logarithmicCoordinatesEquiv n) p)).2 ∈
              angularFundamentalBox (0 : Space n))
        simpa using hp
      have hproj :
          complexTorusCoverProjection n
            ((logarithmicCoordinatesEquiv n) p) =
            realTorusCoverProjection n p := by
        simp [complexTorusCoverProjection]
      by_cases hs : realTorusCoverProjection n p ∈ S
      · have hpre :
            (logarithmicCoordinatesEquiv n) p ∈
              (complexTorusCoverProjection n) ⁻¹' S := by
          simpa [hproj] using hs
        simp only [J, Set.indicator_of_mem hT,
          Set.indicator_of_mem hpre,
          Set.indicator_of_mem hs]
        rw [hproj]
        simp only [complexTorusCoverLift]
        rw [hproj]
        change
          angularWeightedTorusDensity a
              (realTorusCoverProjection n p) *
            ‖torusScalarRepresentative (F k)
                (realTorusCoverProjection n p) -
              f (realTorusCoverProjection n p)‖ ^ 2 =
          angularWeightedTorusDensity a
              (realTorusCoverProjection n p) *
            ‖F k ((logarithmicCoordinatesEquiv n) p) -
              f (realTorusCoverProjection n p)‖ ^ 2
        rw [hrep]
        congr 3
      · have hpre :
            (logarithmicCoordinatesEquiv n) p ∉
              (complexTorusCoverProjection n) ⁻¹' S := by
          simpa [hproj] using hs
        simp [J, Set.indicator_of_mem hT,
          Set.indicator_of_notMem hpre,
          Set.indicator_of_notMem hs]
    · intro p hp
      have hT : (logarithmicCoordinatesEquiv n) p ∉ T := by
        change
          ¬ (((logarithmicCoordinatesEquiv n).symm
            ((logarithmicCoordinatesEquiv n) p)).2 ∈
              angularFundamentalBox (0 : Space n))
        simpa using hp
      simp [J, Set.indicator_of_notMem hT]
  have hmajor (k : ℕ) (z : LogSpace n) :
      0 ≤ J k z ∧
      J k z ≤
        B * K.indicator
          (fun w : LogSpace n =>
            ‖F k w - complexTorusCoverLift f w‖ ^ 2) z := by
    by_cases ht : z ∈ T
    · by_cases hs : complexTorusCoverProjection n z ∈ S
      · let p : Space n × Space n :=
          (logarithmicCoordinatesEquiv n).symm z
        have hpbox : p.2 ∈
            angularFundamentalBox (0 : Space n) := ht
        have hproj : realTorusCoverProjection n p ∈ S := by
          simpa [complexTorusCoverProjection, p] using hs
        have hz : z ∈ K := by
          have hmem :=
            logarithmicPoint_mem_sourceCompactAngularCoverBox
              p hpbox hproj
          have hpoint : logarithmicPoint p.1 p.2 = z := by
            change (logarithmicCoordinatesEquiv n) p = z
            exact (logarithmicCoordinatesEquiv n).apply_symm_apply z
          rw [hpoint] at hmem
          exact hmem
        have hs' :
            z ∈ (complexTorusCoverProjection n) ⁻¹' S := hs
        simp only [J, Set.indicator_of_mem ht,
          Set.indicator_of_mem hs',
          Set.indicator_of_mem hz]
        exact ⟨mul_nonneg
          (angularWeightedTorusDensity_pos a _).le
          (sq_nonneg _),
          mul_le_mul_of_nonneg_right (hB _ hs) (sq_nonneg _)⟩
      · have hs' :
            z ∉ (complexTorusCoverProjection n) ⁻¹' S := hs
        have hright :
            0 ≤ B * K.indicator
              (fun w : LogSpace n =>
                ‖F k w - complexTorusCoverLift f w‖ ^ 2) z := by
          apply mul_nonneg hBpos
          by_cases hz : z ∈ K
          · simp [Set.indicator_of_mem hz]
          · simp [Set.indicator_of_notMem hz]
        simpa [J, Set.indicator_of_mem ht,
          Set.indicator_of_notMem hs'] using
          (show (0 : ℝ) ≤ (0 : ℝ) ∧
            (0 : ℝ) ≤ B * K.indicator
              (fun w : LogSpace n =>
                ‖F k w - complexTorusCoverLift f w‖ ^ 2) z
            from ⟨le_rfl, hright⟩)
    · have hright :
          0 ≤ B * K.indicator
            (fun w : LogSpace n =>
              ‖F k w - complexTorusCoverLift f w‖ ^ 2) z := by
        apply mul_nonneg hBpos
        by_cases hz : z ∈ K
        · simp [Set.indicator_of_mem hz]
        · simp [Set.indicator_of_notMem hz]
      simpa [J, Set.indicator_of_notMem ht] using
        (show (0 : ℝ) ≤ (0 : ℝ) ∧
          (0 : ℝ) ≤ B * K.indicator
            (fun w : LogSpace n =>
              ‖F k w - complexTorusCoverLift f w‖ ^ 2) z
          from ⟨le_rfl, hright⟩)
  have hbound (k : ℕ) :
      (∫ q in S,
        ‖torusScalarRepresentative (F k) q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) ≤
      (logarithmicCoverJacobianFactor n : ℝ) * B *
        (∫ z in K,
          ‖F k z - complexTorusCoverLift f z‖ ^ 2
            ∂(volume : Measure (LogSpace n))) := by
    rw [hident k]
    have hFmem : MemLp (F k) 2
        ((volume : Measure (LogSpace n)).restrict K) := by
      apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
        ((hF k).aestronglyMeasurable.mono_measure
          Measure.restrict_le_self)).mpr
      exact ((hF k).norm.pow 2).continuousOn.integrableOn_compact hK
    have heint :
        IntegrableOn
          (fun z : LogSpace n =>
            ‖F k z - complexTorusCoverLift f z‖ ^ 2)
          K (volume : Measure (LogSpace n)) :=
      (hFmem.sub (hflocal hK)).norm.integrable_sq
    have hupper :
        (∫ z : LogSpace n, J k z
          ∂(volume : Measure (LogSpace n))) ≤
        B *
          (∫ z in K,
            ‖F k z - complexTorusCoverLift f z‖ ^ 2
              ∂(volume : Measure (LogSpace n))) := by
      calc
        (∫ z : LogSpace n, J k z
          ∂(volume : Measure (LogSpace n))) ≤
          ∫ z : LogSpace n,
            B * K.indicator
              (fun w : LogSpace n =>
                ‖F k w - complexTorusCoverLift f w‖ ^ 2) z
            ∂(volume : Measure (LogSpace n)) := by
              apply MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall
                  (fun z => (hmajor k z).1))
                ((heint.integrable_indicator hK.measurableSet).const_mul B)
              exact Filter.Eventually.of_forall
                (fun z => (hmajor k z).2)
        _ = _ := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_indicator hK.measurableSet]
    change
      (logarithmicCoverJacobianFactor n : ℝ) *
          (∫ z : LogSpace n, J k z
            ∂(volume : Measure (LogSpace n))) ≤ _
    calc
      _ ≤ (logarithmicCoverJacobianFactor n : ℝ) *
          (B *
            (∫ z in K,
              ‖F k z - complexTorusCoverLift f z‖ ^ 2
                ∂(volume : Measure (LogSpace n)))) :=
        mul_le_mul_of_nonneg_left hupper
          (NNReal.coe_nonneg _)
      _ = _ := by ring
  apply squeeze_zero
    (fun k => integral_nonneg (fun q => sq_nonneg _))
    hbound
  simpa using
    (hcover hK).const_mul
      ((logarithmicCoverJacobianFactor n : ℝ) * B)
end Ehrhart.TorusStrongWeightedTorusDescent
