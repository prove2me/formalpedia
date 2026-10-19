-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularFourierCoefficient_indexed_finite_sum_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/589aa805-1c8a-48b5-91a3-ac5556a66e6f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_mFourierCoefficient_torusMonomial
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularCharacter_mul_slice_integrable
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_indexedMonomial_finite_sum_ae
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_torusMonomial_angular_memLp

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
    (s : Finset (LatticeAsymptotics.monomialIndex K k))
    (c : LatticeAsymptotics.monomialIndex K k → ℂ)
    (m : Fin n → ℤ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          φ
          (∑ u ∈ s, c u •
            WeightedTorusHilbert.indexedMonomialLp
              K hk hφ hbounded u)
          m x =
        ∑ u ∈ s, c u *
          (if m =
              WeightedTorusHilbert.integerExponent K hk u
            then WeightedTorusHilbert.radialCharacter
              (WeightedTorusHilbert.integerExponent
                K hk u) x
            else 0) := by
  have hrep :=
    indexedMonomial_finite_sum_ae K hk hφ hbounded s c
  unfold WeightedTorusHilbert.weightedTorusMeasure at hrep
  have hslices :=
    MeasureTheory.Measure.ae_ae_eq_curry_of_prod hrep
  filter_upwards [hslices] with x hx
  calc
    HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          φ
          (∑ u ∈ s, c u •
            WeightedTorusHilbert.indexedMonomialLp
              K hk hφ hbounded u)
          m x =
      UnitAddTorus.mFourierCoeff
        (fun θ : TorusCharacters.AngularTorus n =>
          ∑ u ∈ s, c u *
            WeightedTorusHilbert.torusMonomial
              (WeightedTorusHilbert.integerExponent
                K hk u) (x, θ)) m := by
          unfold
            HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
            UnitAddTorus.mFourierCoeff
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hx] with θ hθ
          change
            UnitAddTorus.mFourier (-m) θ •
              (∑ u ∈ s, c u •
                WeightedTorusHilbert.indexedMonomialLp
                  K hk hφ hbounded u) (x, θ) =
            UnitAddTorus.mFourier (-m) θ •
              (∑ u ∈ s, c u *
                WeightedTorusHilbert.torusMonomial
                  (WeightedTorusHilbert.integerExponent
                    K hk u) (x, θ))
          congr 1
    _ = ∑ u ∈ s, c u *
          UnitAddTorus.mFourierCoeff
            (fun θ : TorusCharacters.AngularTorus n =>
              WeightedTorusHilbert.torusMonomial
                (WeightedTorusHilbert.integerExponent
                  K hk u) (x, θ)) m := by
          unfold UnitAddTorus.mFourierCoeff
          simp only [smul_eq_mul, Finset.mul_sum]
          have hint :
              ∀ u ∈ s,
                Integrable
                  (fun θ : TorusCharacters.AngularTorus n =>
                    UnitAddTorus.mFourier (-m) θ *
                      (c u *
                        WeightedTorusHilbert.torusMonomial
                          (WeightedTorusHilbert.integerExponent
                            K hk u) (x, θ)))
                  (volume : Measure
                    (TorusCharacters.AngularTorus n)) := by
            intro u hu
            simpa [WeightedTorusHilbert.angularMeasure] using
              angularCharacter_mul_slice_integrable
              ((torusMonomial_angular_memLp
                (WeightedTorusHilbert.integerExponent
                  K hk u) x).const_mul (c u)) m
          rw [MeasureTheory.integral_finsetSum s hint]
          apply Finset.sum_congr rfl
          intro u hu
          calc
            (∫ θ : TorusCharacters.AngularTorus n,
              UnitAddTorus.mFourier (-m) θ *
                (c u *
                  WeightedTorusHilbert.torusMonomial
                    (WeightedTorusHilbert.integerExponent
                      K hk u) (x, θ))) =
              ∫ θ : TorusCharacters.AngularTorus n,
                c u *
                  (UnitAddTorus.mFourier (-m) θ *
                    WeightedTorusHilbert.torusMonomial
                      (WeightedTorusHilbert.integerExponent
                        K hk u) (x, θ)) := by
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards [] with θ
                    ring
            _ = _ := MeasureTheory.integral_const_mul _ _
    _ = _ := by
      simp_rw [
        HolomorphicLaurentFourierCompletenessBridge.mFourierCoefficient_torusMonomial]
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
