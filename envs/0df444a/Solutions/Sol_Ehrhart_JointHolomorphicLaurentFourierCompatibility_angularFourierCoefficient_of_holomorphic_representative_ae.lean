-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularFourierCoefficient_of_holomorphic_representative_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/09e36e5e-cb44-41af-8e5c-4dbddacef7fc

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_mFourierCoefficient_coverRepresentative_eq_radial

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
    {n k : ℕ}
    {φ : Space n → ℝ}
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hrepresentative :
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z => coverRepresentative F z.1 z.2))
    (m : Fin n → ℤ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          φ f m x =
        UnitAddTorus.mFourierCoeff
            (coverRepresentative F 0) m *
          WeightedTorusHilbert.radialCharacter m x := by
  have hslices :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        (fun θ : TorusCharacters.AngularTorus n =>
          f (x, θ))
          =ᵐ[WeightedTorusHilbert.angularMeasure n]
        (fun θ => coverRepresentative F x θ) := by
    unfold WeightedTorusHilbert.weightedTorusMeasure
      at hrepresentative
    exact MeasureTheory.Measure.ae_ae_eq_curry_of_prod
      hrepresentative
  filter_upwards [hslices] with x hx
  calc
    HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
        φ f m x =
      UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m := by
        unfold
          HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          UnitAddTorus.mFourierCoeff
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hx] with θ hθ
        simp [hθ]
    _ = UnitAddTorus.mFourierCoeff
          (coverRepresentative F 0) m *
        WeightedTorusHilbert.radialCharacter m x :=
      mFourierCoefficient_coverRepresentative_eq_radial
        hF hperiod m x
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
