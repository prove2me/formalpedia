-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.holomorphic_representative_eq_finite_laurent_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/19c3a671-a49d-411f-8eb7-ad83a41a544b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_weightedHilbert_eq_zero_of_angularFourierCoefficients
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularFourierCoefficient_of_holomorphic_representative_ae
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularFourierCoefficient_sub_ae
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularFourierCoefficient_indexed_finite_sum_ae
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_finiteLaurentCoefficient_sum_eq

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
    [Fintype (LatticeAsymptotics.monomialIndex K k)] :
    f =
      ∑ u : LatticeAsymptotics.monomialIndex K k,
        laurentCoefficient F
            (WeightedTorusHilbert.integerExponent
              K hk u) •
          WeightedTorusHilbert.indexedMonomialLp
            K hk hφ hbounded u := by
  classical
  let c : LatticeAsymptotics.monomialIndex K k → ℂ :=
    fun u => laurentCoefficient F
      (WeightedTorusHilbert.integerExponent K hk u)
  let g : WeightedTorusHilbert.weightedHilbert k φ :=
    ∑ u : LatticeAsymptotics.monomialIndex K k,
      c u • WeightedTorusHilbert.indexedMonomialLp
        K hk hφ hbounded u
  have hzero : f - g = 0 := by
    apply
      HolomorphicLaurentFourierCompletenessBridge.weightedHilbert_eq_zero_of_angularFourierCoefficients
        φ (f - g)
    intro m
    have hfcoeff :
        ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
          HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
              φ f m x =
            laurentCoefficient F m *
              WeightedTorusHilbert.radialCharacter m x := by
      simpa [laurentCoefficient] using
        angularFourierCoefficient_of_holomorphic_representative_ae
          f hF hperiod hrepresentative m
    have hgcoeff :
        ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
          HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
              φ g m x =
            ∑ u : LatticeAsymptotics.monomialIndex K k,
              c u *
                (if m =
                    WeightedTorusHilbert.integerExponent
                      K hk u
                  then WeightedTorusHilbert.radialCharacter
                    (WeightedTorusHilbert.integerExponent
                      K hk u) x
                  else 0) := by
      simpa [g] using
        angularFourierCoefficient_indexed_finite_sum_ae
          K hk hφ hbounded Finset.univ c m
    filter_upwards [
      angularFourierCoefficient_sub_ae φ f g m,
      hfcoeff, hgcoeff] with x hx hfx hgx
    rw [hx, hfx, hgx]
    change
      laurentCoefficient F m *
          WeightedTorusHilbert.radialCharacter m x -
        (∑ u : LatticeAsymptotics.monomialIndex K k,
          laurentCoefficient F
              (WeightedTorusHilbert.integerExponent
                K hk u) *
            (if m =
                WeightedTorusHilbert.integerExponent
                  K hk u
              then WeightedTorusHilbert.radialCharacter
                (WeightedTorusHilbert.integerExponent
                  K hk u) x
              else 0)) = 0
    rw [finiteLaurentCoefficient_sum_eq
      K hk hφ hbounded f hF hperiod hrepresentative m x]
    exact sub_self _
  change f = g
  exact sub_eq_zero.mp hzero
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
