-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.eventual_open_momentTorusJetSlope_lt_clampedTailSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/d5d92f59-f424-49c5-b80d-b0a77f6ed8ed

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetGlobalLogKernelEquiLipschitz_exists_open_eventual_log_momentNormalized_diagonalKernel_div_ge_sub_all
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeJointNeighborhoodUpper_upperSemicontinuous_momentTorusClampedTailPositiveSecant
import Theorems.Thm_Ehrhart_BergmanJetTorusSlopeJointNeighborhoodUpper_momentTorusJetSlope_le_tail_zeroTimeSecant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert BergmanMonomials JetEnvelopeRightDerivative
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge BergmanJetGlobalLogKernelEquiLipschitz
open BergmanJetPortmanteauActualUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) (a : ℝ)
    (ha : momentTorusClampedTailPositiveSecant
      K F htransport p r t ht q < a) :
    ∃ (N : ℕ) (U : Set (LogTorus n)),
      IsOpen U ∧ q ∈ U ∧
        ∀ (k : ℕ), N ≤ k → ∀ y ∈ U,
          momentTorusJetSlope K F htransport p k y < a := by
  let G : LogTorus n → ℝ :=
    momentTorusClampedTailPositiveSecant
      K F htransport p r t ht
  let η : ℝ := (a - G q) / 2
  have hη : 0 < η := by
    dsimp [η, G]
    linarith
  have hηt : 0 < η * t := mul_pos hη ht
  obtain ⟨V, hV, hqV, hzero⟩ :=
    exists_open_eventual_log_momentNormalized_diagonalKernel_div_ge_sub_all
      K F htransport q.1 hηt
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hzero
  have hG : UpperSemicontinuous G :=
    upperSemicontinuous_momentTorusClampedTailPositiveSecant
      K F htransport p r t ht
  let W : Set (LogTorus n) :=
    {y : LogTorus n | G y < G q + η} ∩
      ((fun y : LogTorus n => y.1) ⁻¹' V)
  have hW : IsOpen W := by
    exact (hG.isOpen_preimage (G q + η)).inter
      (hV.preimage continuous_fst)
  have hqW : q ∈ W := by
    refine ⟨?_, hqV⟩
    change G q < G q + η
    linarith
  refine ⟨max N₀
    (momentJointTailStart K F htransport p + r + 1),
      W, hW, hqW, ?_⟩
  intro k hk y hy
  have hk₀ : N₀ ≤ k :=
    le_trans (le_max_left _ _) hk
  have hktail :
      momentJointTailStart K F htransport p + r + 1 ≤ k :=
    le_trans (le_max_right _ _) hk
  have hlog := hN₀ k hk₀ y.1 hy.2
  have hfinite := momentTorusJetSlope_le_tail_zeroTimeSecant
    K F htransport p r k hktail y t ht
  have hsec :
      momentTorusTailPositiveSecant
        K F htransport p r t ht y ≤ G y :=
    le_max_right _ _
  have hquot :
      (momentTorusTailUpperEnvelopeTimeSlice
          K F htransport p r t ht y -
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) y.1) /
              (k : ℝ)) / t ≤
      momentTorusTailPositiveSecant
          K F htransport p r t ht y + η := by
    unfold momentTorusTailPositiveSecant
    apply (div_le_iff₀ ht).mpr
    have hlog' := hlog
    field_simp [ht.ne']
    linarith
  have hyG : G y < G q + η := hy.1
  calc
    momentTorusJetSlope K F htransport p k y ≤
      (momentTorusTailUpperEnvelopeTimeSlice
          K F htransport p r t ht y -
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) y.1) /
              (k : ℝ)) / t := hfinite
    _ ≤ momentTorusTailPositiveSecant
        K F htransport p r t ht y + η := hquot
    _ ≤ G y + η := by linarith
    _ < a := by
      dsimp [η] at hyG ⊢
      linarith
end Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
