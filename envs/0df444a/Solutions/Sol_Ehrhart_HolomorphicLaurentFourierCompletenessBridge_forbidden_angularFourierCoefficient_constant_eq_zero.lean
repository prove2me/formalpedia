-- Prove2me | solution 1 for Ehrhart.HolomorphicLaurentFourierCompletenessBridge.forbidden_angularFourierCoefficient_constant_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:12.519086+00:00
-- url     : https://prove2.me/submissions/cd01ef0e-70cf-4b10-9084-7e502da1ddb2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MonomialDivergence_not_integrable_monomialWeight_of_centeredBody_not_mem_interior
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_angularFourierCoefficient_sq_integrable
import Theorems.Thm_Ehrhart_HolomorphicLaurentFourierCompletenessBridge_radialCharacter_sq_integrable_iff_monomialWeight

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
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u)
    (hu : u ∉ interior K.carrier)
    (c : ℂ)
    (hcoefficient :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        angularFourierCoefficient φ f m x =
          c * WeightedTorusHilbert.radialCharacter m x) :
    c = 0 := by
  by_contra hc
  have hsq := angularFourierCoefficient_sq_integrable φ f m
  have hscaled :
      Integrable
        (fun x : Space n =>
          ‖c‖ ^ 2 *
            ‖WeightedTorusHilbert.radialCharacter m x‖ ^ 2)
        (WeightedTorusHilbert.radialMeasure k φ) := by
    apply hsq.congr
    filter_upwards [hcoefficient] with x hx
    rw [hx, norm_mul, mul_pow]
  have hcnorm : ‖c‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
  have hradial :
      Integrable
        (fun x : Space n =>
          ‖WeightedTorusHilbert.radialCharacter m x‖ ^ 2)
        (WeightedTorusHilbert.radialMeasure k φ) := by
    have h := hscaled.const_mul (‖c‖ ^ 2)⁻¹
    simpa [← mul_assoc, hcnorm] using h
  have hmono :=
    (radialCharacter_sq_integrable_iff_monomialWeight
      k hφ m u hm).mp hradial
  have hupper : ∀ x : Space n,
      φ x ≤ SupportFunction.supportFunction K.carrier x + C := by
    intro x
    have h := (abs_le.mp (hbounded x)).2
    linarith
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  exact MonomialDivergence.not_integrable_monomialWeight_of_centeredBody_not_mem_interior
    K hu hupper hkreal hmono
end Ehrhart.HolomorphicLaurentFourierCompletenessBridge
