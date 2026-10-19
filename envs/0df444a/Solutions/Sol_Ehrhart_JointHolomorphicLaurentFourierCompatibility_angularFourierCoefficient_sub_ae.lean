-- Prove2me | solution 1 for Ehrhart.JointHolomorphicLaurentFourierCompatibility.angularFourierCoefficient_sub_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/00270cae-09a4-4fec-aa8f-b604f2dfcea4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_angularSlice_memLp_ae
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_angularCharacter_mul_slice_integrable

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
    {n k : ℕ} (φ : Space n → ℝ)
    (f g : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          φ (f - g) m x =
        HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
            φ f m x -
          HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
            φ g m x := by
  have hsub := MeasureTheory.Lp.coeFn_sub f g
  unfold WeightedTorusHilbert.weightedTorusMeasure at hsub
  have hslices :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        (fun θ : TorusCharacters.AngularTorus n =>
          (f - g) (x, θ))
          =ᵐ[WeightedTorusHilbert.angularMeasure n]
        (fun θ => f (x, θ) - g (x, θ)) := by
    filter_upwards [MeasureTheory.Measure.ae_ae_eq_curry_of_prod hsub]
      with x hx
    filter_upwards [hx] with θ hθ
    exact hθ
  filter_upwards [hslices,
    HolomorphicLaurentFourierCompletenessBridge.angularSlice_memLp_ae φ f,
    HolomorphicLaurentFourierCompletenessBridge.angularSlice_memLp_ae φ g]
    with x hx hfx hgx
  unfold HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
    UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  calc
    (∫ θ : TorusCharacters.AngularTorus n,
      UnitAddTorus.mFourier (-m) θ * (f - g) (x, θ)) =
      ∫ θ : TorusCharacters.AngularTorus n,
        (UnitAddTorus.mFourier (-m) θ * f (x, θ) -
          UnitAddTorus.mFourier (-m) θ * g (x, θ)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hx] with θ hθ
        rw [hθ]
        ring
    _ = _ := MeasureTheory.integral_sub
      (angularCharacter_mul_slice_integrable hfx m)
      (angularCharacter_mul_slice_integrable hgx m)
end Ehrhart.JointHolomorphicLaurentFourierCompatibility
