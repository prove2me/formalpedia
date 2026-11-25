-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_eq_one_of_restrictIdeal_eq_coordIdeal_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:51.540986+00:00
-- url     : https://prove2.me/submissions/f20217b0-500f-4191-b9b8-2d9aff811859

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_CoordinateIdealOrderOne
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_coord_notMem_maximalIdeal_sq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_maximalIdeal_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_stalkIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_orderAt_iff_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_zero_iff_not_mem_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
private theorem le_one_of_not_two_le {a : ℕ∞} (h : ¬ ((2 : ℕ) : ℕ∞) ≤ a) : a ≤ 1 := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact absurd le_top h
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    have hm : ¬ (2 ≤ m) := fun hh => h (by exact_mod_cast hh)
    have hm1 : m ≤ 1 := by omega
    exact_mod_cast hm1
private theorem orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (c : EtaleChart p V n) (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal S) (y : X) (hy : y ∈ V) :
    orderAt D y ≤ 1 := by
  classical
  by_cases hys : y ∈ D.support
  · have hgerm : (X.presheaf.germ V y hy).hom (c.coord j) ∈ stalkIdeal D y := by
      refine germ_mem_stalkIdeal D y ⟨V, hV⟩ hy ?_
      rw [EtaleChart.ideal_eq_span_coord c hV D S hD]
      exact Ideal.subset_span ⟨j, Finset.mem_coe.mpr hj, rfl⟩
    have hmax : stalkIdeal D y ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
      (mem_support_iff_stalkIdeal_le_maximalIdeal D y).mp hys
    have hmem : c.coord j ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal :=
      (germ_mem_maximalIdeal_iff hV y hy (c.coord j)).mp (hmax hgerm)
    refine le_one_of_not_two_le ?_
    intro h2
    rw [le_orderAt_iff] at h2
    exact germ_coord_notMem_maximalIdeal_sq p hV c j y hy hmem (h2 hgerm)
  · rw [(orderAt_eq_zero_iff_not_mem_support D y).mpr hys]
    exact zero_le_one
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {V : X.Opens}
    (hV : IsAffineOpen V) {n : ℕ} (c : EtaleChart p V n) (j : Fin n) (D : X.IdealSheafData)
    (hD : restrictIdeal D V = c.coordIdeal {j}) (y : X) (hy : y ∈ V) (hys : y ∈ D.support) :
    orderAt D y = 1 :=
  le_antisymm (orderAt_le_one_of_mem_of_restrictIdeal_eq_coordIdeal p hV c {j} j (Finset.mem_singleton_self j) D hD y hy)
    ((one_le_orderAt_iff_mem_support D y).mpr hys)
end FunctorialResolution.EmbeddedResolution
