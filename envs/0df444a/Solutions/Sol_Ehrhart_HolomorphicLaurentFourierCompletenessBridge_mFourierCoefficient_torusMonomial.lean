-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.mFourierCoefficient_torusMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/ca40570d-fd86-4f60-b6e3-4e30bcf0311b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution {n : ℕ}
    (m q : Fin n → ℤ) (x : Space n) :
    UnitAddTorus.mFourierCoeff
      (fun θ : TorusCharacters.AngularTorus n =>
        WeightedTorusHilbert.torusMonomial q (x, θ)) m =
      if m = q then
        WeightedTorusHilbert.radialCharacter q x
      else 0 := by
  unfold UnitAddTorus.mFourierCoeff
    WeightedTorusHilbert.torusMonomial
  calc
    (∫ θ : TorusCharacters.AngularTorus n,
      UnitAddTorus.mFourier (-m) θ •
        (WeightedTorusHilbert.radialCharacter q x *
          UnitAddTorus.mFourier q θ)) =
      ∫ θ : TorusCharacters.AngularTorus n,
        WeightedTorusHilbert.radialCharacter q x *
          (conj (UnitAddTorus.mFourier m θ) *
            UnitAddTorus.mFourier q θ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with θ
      rw [UnitAddTorus.mFourier_neg]
      simp [smul_eq_mul]
      ring
    _ = WeightedTorusHilbert.radialCharacter q x *
        (∫ θ : TorusCharacters.AngularTorus n,
          conj (UnitAddTorus.mFourier m θ) *
            UnitAddTorus.mFourier q θ) :=
      MeasureTheory.integral_const_mul _ _
    _ = _ := by
      have hinner :
          (∫ θ : TorusCharacters.AngularTorus n,
            conj (UnitAddTorus.mFourier m θ) *
              UnitAddTorus.mFourier q θ) =
            if m = q then (1 : ℂ) else 0 := by
        simpa [WeightedTorusHilbert.angularMeasure] using
          WeightedTorusHilbert.angularCharacter_inner m q
      rw [hinner]
      split_ifs <;> simp
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
