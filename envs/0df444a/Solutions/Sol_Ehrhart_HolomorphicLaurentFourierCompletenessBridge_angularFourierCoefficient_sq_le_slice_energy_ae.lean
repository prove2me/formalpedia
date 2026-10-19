-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient_sq_le_slice_energy_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/48ebacce-ffbf-4030-9837-ace419e55fd7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_angularSlice_memLp_ae

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.HolomorphicLaurentFourierCompletenessBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13449
attribute [local instance] Ehrhart.HolomorphicLaurentFourierCompletenessBridge._p2m_local_instance_3610026555_13452
namespace Ehrhart.HolomorphicLaurentFourierCompletenessBridge
theorem _root_.solution {n k : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      ‖angularFourierCoefficient φ f m x‖ ^ 2 ≤
        ∫ θ : TorusCharacters.AngularTorus n,
          ‖f (x, θ)‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n) := by
  filter_upwards [angularSlice_memLp_ae φ f] with x hx
  let fx : MeasureTheory.Lp ℂ 2
      (WeightedTorusHilbert.angularMeasure n) :=
    hx.toLp (fun θ : TorusCharacters.AngularTorus n =>
      f (x, θ))
  have hfx :
      (fun θ : TorusCharacters.AngularTorus n =>
        fx θ) =ᵐ[WeightedTorusHilbert.angularMeasure n]
          (fun θ => f (x, θ)) :=
    hx.coeFn_toLp
  have hcoeff :
      UnitAddTorus.mFourierCoeff
        (fun θ : TorusCharacters.AngularTorus n => fx θ) m =
        angularFourierCoefficient φ f m x := by
    unfold angularFourierCoefficient UnitAddTorus.mFourierCoeff
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hfx] with θ hθ
    simp [hθ]
  have henergy :
      (∫ θ : TorusCharacters.AngularTorus n,
        ‖fx θ‖ ^ 2 ∂(WeightedTorusHilbert.angularMeasure n)) =
        ∫ θ : TorusCharacters.AngularTorus n,
          ‖f (x, θ)‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hfx] with θ hθ
    rw [hθ]
  have hparse := UnitAddTorus.hasSum_sq_mFourierCoeff fx
  have hle := le_hasSum hparse m (fun j hj => sq_nonneg _)
  rw [← hcoeff, ← henergy]
  exact hle
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
