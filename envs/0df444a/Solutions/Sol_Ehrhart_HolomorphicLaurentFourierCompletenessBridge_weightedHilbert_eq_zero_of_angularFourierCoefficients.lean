-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.weightedHilbert_eq_zero_of_angularFourierCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/b94bded5-265f-43ac-9dd9-431021d395c7

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
theorem _root_.solution
    {n k : ℕ} (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (hcoeff : ∀ m : Fin n → ℤ,
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        angularFourierCoefficient φ f m x = 0) :
    f = 0 := by
  have hall :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        ∀ m : Fin n → ℤ, angularFourierCoefficient φ f m x = 0 :=
    MeasureTheory.ae_all_iff.mpr hcoeff
  have henergy :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        (∫ θ : TorusCharacters.AngularTorus n,
          ‖f (x, θ)‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n)) = 0 := by
    filter_upwards [hall, angularSlice_memLp_ae φ f] with x hx hmem
    let fx : MeasureTheory.Lp ℂ 2
        (WeightedTorusHilbert.angularMeasure n) :=
      hmem.toLp
        (fun θ : TorusCharacters.AngularTorus n =>
          f (x, θ))
    have hfx :
        (fun θ : TorusCharacters.AngularTorus n => fx θ)
          =ᵐ[WeightedTorusHilbert.angularMeasure n]
            (fun θ => f (x, θ)) :=
      hmem.coeFn_toLp
    have hzero :
        ∀ m : Fin n → ℤ,
          UnitAddTorus.mFourierCoeff
            (fun θ : TorusCharacters.AngularTorus n =>
              fx θ) m = 0 := by
      intro m
      calc
        UnitAddTorus.mFourierCoeff
            (fun θ : TorusCharacters.AngularTorus n => fx θ) m =
          angularFourierCoefficient φ f m x := by
            unfold angularFourierCoefficient UnitAddTorus.mFourierCoeff
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hfx] with θ hθ
            simp [hθ]
        _ = 0 := hx m
    have hparse := UnitAddTorus.hasSum_sq_mFourierCoeff fx
    have hsumzero :
        HasSum (fun _m : Fin n → ℤ => (0 : ℝ))
          (∫ θ : TorusCharacters.AngularTorus n,
            ‖fx θ‖ ^ 2
            ∂(WeightedTorusHilbert.angularMeasure n)) := by
      change HasSum
        (fun m : Fin n → ℤ =>
          ‖UnitAddTorus.mFourierCoeff
            (fun θ : TorusCharacters.AngularTorus n =>
              fx θ) m‖ ^ 2)
        (∫ θ : TorusCharacters.AngularTorus n,
          ‖fx θ‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n)) at hparse
      simpa [hzero] using hparse
    have hz :
        (∫ θ : TorusCharacters.AngularTorus n,
          ‖fx θ‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n)) = 0 :=
      hsumzero.unique hasSum_zero
    calc
      (∫ θ : TorusCharacters.AngularTorus n,
        ‖f (x, θ)‖ ^ 2
        ∂(WeightedTorusHilbert.angularMeasure n)) =
        ∫ θ : TorusCharacters.AngularTorus n,
          ‖fx θ‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hfx] with θ hθ
        rw [hθ]
      _ = 0 := hz
  have hsquare :
      Integrable
        (fun z : WeightedTorusHilbert.LogTorus n =>
          ‖f z‖ ^ 2)
        (WeightedTorusHilbert.weightedTorusMeasure k φ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (MeasureTheory.Lp.aestronglyMeasurable f)).mp
        (MeasureTheory.Lp.memLp f)
  have hintegral :
      (∫ z : WeightedTorusHilbert.LogTorus n,
        ‖f z‖ ^ 2
        ∂(WeightedTorusHilbert.weightedTorusMeasure k φ)) =
        0 := by
    unfold WeightedTorusHilbert.weightedTorusMeasure at hsquare ⊢
    rw [MeasureTheory.integral_prod _ hsquare]
    exact MeasureTheory.integral_eq_zero_of_ae henergy
  have hzero :
      (fun z : WeightedTorusHilbert.LogTorus n =>
        ‖f z‖ ^ 2)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
          0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun z => sq_nonneg _) hsquare).mp hintegral
  apply MeasureTheory.Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero] with z hz
  have hnorm : ‖f z‖ = 0 := by
    exact sq_eq_zero_iff.mp (by simpa using hz)
  exact norm_eq_zero.mp hnorm
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
