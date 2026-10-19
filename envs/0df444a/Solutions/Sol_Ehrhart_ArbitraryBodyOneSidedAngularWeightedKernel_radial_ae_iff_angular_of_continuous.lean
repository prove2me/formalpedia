-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.radial_ae_iff_angular_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/3dc983c1-ee0d-4f99-a9ff-a7277fa4d01a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_angularWeightedTorusDensity_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation JetEnvelopeSlopeConvergence
open ComplexKillingSaturationBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (P : LogTorus n → Prop) :
    (∀ᵐ q ∂(weightedTorusMeasure 1 φ), P q) ↔
      ∀ᵐ q ∂(angularWeightedTorusMeasure a), P q := by
  rw [weightedTorusMeasure_eq_withDensity 1 hφ]
  change
    (∀ᵐ q ∂(sourceTorusBaseMeasure n).withDensity
      (fun q : LogTorus n => radialWeight 1 φ q.1), P q) ↔
    ∀ᵐ q ∂(sourceTorusBaseMeasure n).withDensity
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a q)), P q
  have hrad :
      Measurable
        (fun q : LogTorus n => radialWeight 1 φ q.1) :=
    (radialWeight_measurable 1 hφ).comp measurable_fst
  have hang :
      Measurable
        (fun q : LogTorus n =>
          ENNReal.ofReal (angularWeightedTorusDensity a q)) :=
    (continuous_angularWeightedTorusDensity ha).measurable.ennreal_ofReal
  rw [MeasureTheory.ae_withDensity_iff hrad,
    MeasureTheory.ae_withDensity_iff hang]
  constructor
  · intro hP
    filter_upwards [hP] with q hq hne
    apply hq
    have hpos : 0 < radialWeight 1 φ q.1 := by
      unfold radialWeight
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    exact hpos.ne'
  · intro hP
    filter_upwards [hP] with q hq hne
    apply hq
    exact (ENNReal.ofReal_pos.mpr
      (angularWeightedTorusDensity_pos a q)).ne'
end Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
