-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:07:14.610697+00:00
-- url     : https://prove2.me/submissions/c6a3652c-b016-4e99-ab75-b653916d0a28

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivBalancedOrderLocus
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsDerivBalanced_derivIdealSheafIterate_pow_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_coordBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_tensorKaehlerBasis_mapBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_maxContactIdeal_eq_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_zero_iff_not_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_le_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_derivIdealSheafIterate_eq_orderAtLeastLocus
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.coordBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.tensorKaehlerBasis_mapBaseChange
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply



set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
  (I : X.IdealSheafData) (m : ℕ)
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    (h : IsDerivBalanced k p I m) (x : X) :
    orderAt I x = 0 ∨ (m : ℕ∞) ≤ orderAt I x := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · right
    simp
  have hm1 : 1 ≤ m := hpos
  by_cases h0 : orderAt I x = 0
  · exact Or.inl h0
  right
  have hlt : m - 1 < m := by omega
  have hle : derivIdealSheafIterate k p (m - 1) I ^ m ≤ I ^ (m - (m - 1)) :=
    IsDerivBalanced.derivIdealSheafIterate_pow_le k p h hlt
  have hsub : m - (m - 1) = 1 := by omega
  rw [hsub, pow_one] at hle
  have hord : orderAt I x ≤ orderAt (derivIdealSheafIterate k p (m - 1) I ^ m) x :=
    orderAt_le_of_le hle x
  rw [orderAt_pow k p (derivIdealSheafIterate k p (m - 1) I) m x] at hord
  have hne : orderAt (derivIdealSheafIterate k p (m - 1) I) x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hord
    exact h0 (le_antisymm hord (by exact zero_le))
  have hmem : x ∈ (derivIdealSheafIterate k p (m - 1) I).support := by
    by_contra hc
    exact hne ((orderAt_eq_zero_iff_not_mem_support _ x).mpr hc)
  have heq := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1
  have hx : x ∈ orderAtLeastLocus I m := by
    rw [← heq]
    exact hmem
  exact (mem_orderAtLeastLocus_iff I m x).mp hx
end FunctorialResolution.EmbeddedResolution
