-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularToRadialGraphAmbientCLMOfUpper_smooth_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/04446c91-f634-4e27-abec-1e1da7a7c371

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularToRadialLpOfUpper_ae_eq

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
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    {v : angularDolbeaultGraphAmbient a}
    (hv : v ∈ smoothAngularDolbeaultGraphSet a) :
    angularToRadialGraphAmbientCLMOfUpper hφ hupper v ∈
      smoothFunctionDolbeaultGraphSet 1 φ := by
  obtain ⟨F, hF, hperiod, hcompact, hf, hd, rfl⟩ := hv
  let hf' := memLp_radial_of_angular_upper hφ hupper hf
  let hd' := memLp_radial_of_angular_upper hφ hupper hd
  refine ⟨F, hF, hperiod, hcompact, hf', hd', ?_⟩
  rw [angularToRadialGraphAmbientCLMOfUpper_pair]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · apply MeasureTheory.Lp.ext
    filter_upwards [
      angularToRadialLpOfUpper_ae_eq hφ hupper
        (angularScalarL2OfRepresentative a F hf),
      (Measure.absolutelyContinuous_of_le_smul
        (radialWeightedTorusMeasure_le_angular_of_upper
          hφ hupper)).ae_eq hf.coeFn_toLp,
      hf'.coeFn_toLp]
        with q htransfer hsource hradial
    exact htransfer.trans (hsource.trans hradial.symm)
  · apply MeasureTheory.Lp.ext
    filter_upwards [
      angularToRadialLpOfUpper_ae_eq hφ hupper
        (angularBarPartialL2OfRepresentative a F hd),
      (Measure.absolutelyContinuous_of_le_smul
        (radialWeightedTorusMeasure_le_angular_of_upper
          hφ hupper)).ae_eq hd.coeFn_toLp,
      hd'.coeFn_toLp]
        with q htransfer hsource hradial
    exact htransfer.trans (hsource.trans hradial.symm)
end Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
