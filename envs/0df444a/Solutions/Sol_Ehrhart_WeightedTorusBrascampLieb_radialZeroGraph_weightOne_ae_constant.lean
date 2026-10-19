-- Prove2me | solution 1 for Ehrhart.WeightedTorusBrascampLieb.radialZeroGraph_weightOne_ae_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/db6fca1a-ed64-4b16-beda-df83b221b256

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusHilbert_indexedMonomialLp_ae
import Theorems.Thm_Ehrhart_ComplexSaturatedKillingFieldBridge_weightOne_integerExponent_eq_zero
import Theorems.Thm_Ehrhart_ComplexSaturatedKillingFieldBridge_torusMonomial_zero
import Theorems.Thm_Ehrhart_WeightedTorusBrascampLieb_radialZeroGraph_weightOne_eq_constantMonomial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusBrascampLieb
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open ComplexSaturatedKillingFieldBridge WeightedTorusWeylWeakRepresentativeBridge
open JointHolomorphicLaurentFourierCompatibility WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusBrascampLieb
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {B : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction
        K.carrier x| ≤ B)
    (f : weightedTorusScalarL2 1 φ)
    (hf : WithLp.toLp 2
      (f, (0 : weightedTorusFormL2 1 φ)) ∈
        functionDolbeaultGraph 1 φ) :
    ∃ c : ℂ, (fun q : LogTorus n => f q) =ᵐ[
      weightedTorusMeasure 1 φ] (fun _ => c) := by
  obtain ⟨c, hc⟩ := radialZeroGraph_weightOne_eq_constantMonomial
    K hφ hbounded f hf
  let u := weightOneZeroIndex K
  let M : weightedTorusScalarL2 1 φ :=
    indexedMonomialLp K (by decide) hφ hbounded u
  refine ⟨c, ?_⟩
  have hmonomial := indexedMonomialLp_ae
    K (by decide) hφ hbounded u
  have hsmul := MeasureTheory.Lp.coeFn_smul c M
  filter_upwards [hmonomial, hsmul] with q hmono hmul
  calc
    f q = (c • M) q := by rw [hc]
    _ = c • M q := hmul
    _ = c := by
      rw [hmono, weightOne_integerExponent_eq_zero,
        torusMonomial_zero]
      simp
end Ehrhart.WeightedTorusBrascampLieb
