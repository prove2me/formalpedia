-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:40:41.329862+00:00
-- url     : https://prove2.me/submissions/c62ff0af-f46f-48cd-80c0-1096588434e5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_comap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_le_orderAt_comap
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_comap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_derivIdealSheafIterate_eq_sub
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem le_natCast_or_succ_le (a : ℕ∞) (r : ℕ) :
    a ≤ (r : ℕ∞) ∨ ((r + 1 : ℕ) : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact Or.inr le_top
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 ha
    rcases Nat.lt_or_ge r m with hm | hm
    · exact Or.inr (by exact_mod_cast hm)
    · exact Or.inl (by exact_mod_cast hm)
private theorem one_le_orderAt_of_one_le_orderAt_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (J : X.IdealSheafData)
    (y : Y) (hy : (1 : ℕ∞) ≤ orderAt (J.comap h) y) : (1 : ℕ∞) ≤ orderAt J (h.base y) := by
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (J.comap h) y := by exact_mod_cast hy
  suffices hs : ((1 : ℕ) : ℕ∞) ≤ orderAt J (h.base y) by exact_mod_cast hs
  rw [le_orderAt_iff] at h1 ⊢
  rw [stalkIdeal_comap, pow_one] at h1
  rw [pow_one]
  simpa only [IsLocalRing.maximalIdeal_comap] using
    Ideal.le_comap_map.trans (Ideal.comap_mono h1)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] (I : X.IdealSheafData) (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  have : LocallyOfFiniteType p := inferInstance
  have : LocallyOfFiniteType (h ≫ p) := inferInstance
  refine le_antisymm ?_ (orderAt_le_orderAt_comap h I y)
  rcases eq_or_ne (orderAt I (h.base y)) ⊤ with hI | hI
  · rw [hI]; exact le_top
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 hI
  rw [← hr]
  rcases le_natCast_or_succ_le (orderAt (I.comap h) y) r with hle | hlt
  · exact hle
  exfalso
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (derivIdealSheafIterate k (h ≫ p) r (I.comap h)) y :=
    le_orderAt_derivIdealSheafIterate k (h ≫ p) (I.comap h) y 1 r (by
      rw [Nat.add_comm]; exact hlt)
  rw [derivIdealSheafIterate_comap k p h r I] at h1
  have h2 : (1 : ℕ∞) ≤ orderAt ((derivIdealSheafIterate k p r I).comap h) y := by exact_mod_cast h1
  have h3 := one_le_orderAt_of_one_le_orderAt_comap h (derivIdealSheafIterate k p r I) y h2
  have h4 : orderAt (derivIdealSheafIterate k p r I) (h.base y) = ((r - r : ℕ) : ℕ∞) :=
    orderAt_derivIdealSheafIterate_eq_sub k p I (h.base y) hr.symm (le_refl r)
  rw [h4, Nat.sub_self] at h3
  simp at h3
end FunctorialResolution.EmbeddedResolution
