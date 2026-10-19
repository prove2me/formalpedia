-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.upperSemicontinuous_momentTorusTailPositiveSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/8473b0df-d4c0-4244-841b-d6a20004be6f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualUpperTailBridge_upperSemicontinuous_momentTorusTailUpperEnvelopeTimeSlice

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
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    UpperSemicontinuous
      (momentTorusTailPositiveSecant
        K F htransport p r t ht) := by
  have htail :=
    upperSemicontinuous_momentTorusTailUpperEnvelopeTimeSlice
      K F htransport p r t ht
  have hpot : Continuous
      (fun q : LogTorus n =>
        -momentNormalizedPotential F q.1) :=
    ((continuous_momentNormalizedPotential F).comp
      continuous_fst).neg
  have hsub : UpperSemicontinuous
      (fun q : LogTorus n =>
        momentTorusTailUpperEnvelopeTimeSlice
            K F htransport p r t ht q +
          -momentNormalizedPotential F q.1) :=
    htail.add hpot.upperSemicontinuous
  have hscale : Continuous (fun x : ℝ => x / t) :=
    continuous_id.div_const t
  have hmono : Monotone (fun x : ℝ => x / t) := by
    intro a b hab
    exact (div_le_div_iff_of_pos_right ht).mpr hab
  have h := hscale.comp_upperSemicontinuous hsub hmono
  have hsecant :
      ((fun x : ℝ => x / t) ∘
        (fun q : LogTorus n =>
          momentTorusTailUpperEnvelopeTimeSlice
              K F htransport p r t ht q +
            -momentNormalizedPotential F q.1)) =
        momentTorusTailPositiveSecant
          K F htransport p r t ht := by
    funext q
    dsimp [momentTorusTailPositiveSecant, Function.comp_def]
    ring
  rw [hsecant] at h
  exact h
end Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
