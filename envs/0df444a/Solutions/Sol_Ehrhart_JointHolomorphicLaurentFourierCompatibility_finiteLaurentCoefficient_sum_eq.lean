-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.finiteLaurentCoefficient_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/7504bc66-bdb6-4ef4-9544-3f726755fcff

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_forbidden_coefficient_of_holomorphic_representative_eq_zero
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_integerPoint_eq_smul_scaledExponent
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_scaledExponent_mem_monomialIndex_iff
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_scaledExponent_integerExponent
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_integerExponent_eq_of_integerPoint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13915
attribute [local instance] Ehrhart.JointHolomorphicLaurentFourierCompatibility._p2m_local_instance_3610026555_13918
namespace Ehrhart.JointHolomorphicLaurentFourierCompatibility
theorem _root_.solution
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hrepresentative :
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z => coverRepresentative F z.1 z.2))
    [Fintype (LatticeAsymptotics.monomialIndex K k)]
    (m : Fin n → ℤ) (x : Space n) :
    (∑ u : LatticeAsymptotics.monomialIndex K k,
      laurentCoefficient F
          (WeightedTorusHilbert.integerExponent K hk u) *
        (if m = WeightedTorusHilbert.integerExponent K hk u
          then WeightedTorusHilbert.radialCharacter
            (WeightedTorusHilbert.integerExponent K hk u) x
          else 0)) =
      laurentCoefficient F m *
        WeightedTorusHilbert.radialCharacter m x := by
  classical
  by_cases hinside : scaledExponent k m ∈ interior K.carrier
  · let u : LatticeAsymptotics.monomialIndex K k :=
      ⟨scaledExponent k m,
        (scaledExponent_mem_monomialIndex_iff
          K hk m).mpr hinside⟩
    have huexp :
        WeightedTorusHilbert.integerExponent K hk u = m := by
      apply integerExponent_eq_of_integerPoint K hk u m
      exact integerPoint_eq_smul_scaledExponent hk m
    calc
      (∑ v : LatticeAsymptotics.monomialIndex K k,
        laurentCoefficient F
            (WeightedTorusHilbert.integerExponent K hk v) *
          (if m = WeightedTorusHilbert.integerExponent
              K hk v
            then WeightedTorusHilbert.radialCharacter
              (WeightedTorusHilbert.integerExponent
                K hk v) x
            else 0)) =
        laurentCoefficient F
            (WeightedTorusHilbert.integerExponent K hk u) *
          (if m = WeightedTorusHilbert.integerExponent
              K hk u
            then WeightedTorusHilbert.radialCharacter
              (WeightedTorusHilbert.integerExponent
                K hk u) x
            else 0) := by
          apply Finset.sum_eq_single u
          · intro v hv hvne
            have hne :
                m ≠ WeightedTorusHilbert.integerExponent
                  K hk v := by
              intro hmv
              apply hvne
              apply WeightedTorusHilbert.integerExponent_injective
                K hk
              exact hmv.symm.trans huexp.symm
            simp [hne]
          · simp
      _ = _ := by simp [huexp]
  · have hcoefficient :
        laurentCoefficient F m = 0 := by
      exact forbidden_coefficient_of_holomorphic_representative_eq_zero
        K hk hφ hbounded f hF hperiod hrepresentative
        m (scaledExponent k m)
        (integerPoint_eq_smul_scaledExponent hk m) hinside
    have hnone :
        ∀ u : LatticeAsymptotics.monomialIndex K k,
          m ≠ WeightedTorusHilbert.integerExponent K hk u := by
      intro u hmu
      apply hinside
      rw [hmu, scaledExponent_integerExponent K hk u]
      exact u.property.1
    simp [hnone, hcoefficient]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
