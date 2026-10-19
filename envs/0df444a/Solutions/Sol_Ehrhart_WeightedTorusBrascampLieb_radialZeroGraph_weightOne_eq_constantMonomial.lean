-- Prove2me | solution 1 for Ehrhart.WeightedTorusBrascampLieb.radialZeroGraph_weightOne_eq_constantMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/eb147abb-16c6-4b07-a0ab-57340d14e6bf

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_holomorphic_representative_eq_finite_laurent_sum
import Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_weightedZeroGraph_exists_periodic_holomorphic_representative
import Theorems.Thm_Ehrhart_ComplexSaturatedKillingFieldBridge_weightedTorus_representative_ae_of_complexCover
import Theorems.Thm_Ehrhart_ComplexSaturatedKillingFieldBridge_weightOneIndex_eq_zeroIndex
import Theorems.Thm_Ehrhart_ComplexSaturatedKillingFieldBridge_weightOne_integerExponent_eq_zero

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
    ∃ c : ℂ,
      f = c • indexedMonomialLp K (by decide) hφ hbounded
        (weightOneZeroIndex K) := by
  classical
  let := (BergmanMonomials.monomialIndex_finite
    K (by decide : 0 < (1 : ℕ))).fintype
  obtain ⟨F, hF, hperiod, hcover⟩ :=
    weightedZeroGraph_exists_periodic_holomorphic_representative
      hφ f hf
  have hfinite := holomorphic_representative_eq_finite_laurent_sum
    K (by decide) hφ hbounded f hF hperiod
      (weightedTorus_representative_ae_of_complexCover hφ hcover)
  have hsingleton :
      (Finset.univ : Finset
        (LatticeAsymptotics.monomialIndex K 1)) =
          {weightOneZeroIndex K} := by
    ext u
    simp [weightOneIndex_eq_zeroIndex K u]
  refine ⟨laurentCoefficient F (0 : Fin n → ℤ), ?_⟩
  simpa only [hsingleton, Finset.sum_singleton,
    weightOne_integerExponent_eq_zero] using hfinite
end Ehrhart.WeightedTorusBrascampLieb
