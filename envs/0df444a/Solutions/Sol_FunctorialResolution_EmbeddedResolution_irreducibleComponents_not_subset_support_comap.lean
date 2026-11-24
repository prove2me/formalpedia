-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.irreducibleComponents_not_subset_support_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:46.840542+00:00
-- url     : https://prove2.me/submissions/bc209b0d-0a49-4c06-b392-0837f5ef21fa

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplittingFlatPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mem_support_comap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (h : Y ⟶ X) (hg : GeneralizingMap (fun y : Y => h.base y))
    (E : List X.IdealSheafData) (N : X.IdealSheafData)
    (hN : ∀ D ∈ E, ∀ C : Set X, IsIrreducible C → C ⊆ (D.support : Set X) →
      (∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C) →
      ¬ C ⊆ (N.support : Set X)) :
    ∀ D ∈ E.map (fun D : X.IdealSheafData => D.comap h), ∀ C : Set Y, IsIrreducible C →
      C ⊆ (D.support : Set Y) →
      (∀ C' : Set Y, IsIrreducible C' → C' ⊆ (D.support : Set Y) → C ⊆ C' → C' ⊆ C) →
      ¬ C ⊆ ((N.comap h).support : Set Y) := by
  rintro D' hD' C hC hCsub hCmax hCN
  obtain ⟨D, hD, hDD⟩ := List.mem_map.mp hD'
  have hDD' : D' = D.comap h := hDD.symm
  subst hDD'
  have hCclosed : IsClosed C := by
    rw [← closure_subset_iff_isClosed]
    exact hCmax (closure C) hC.closure
      (closure_minimal hCsub (D.comap h).support.isClosed) subset_closure
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC hCclosed
  have hξC : ξ ∈ C := by
    rw [← hξ]
    exact subset_closure (Set.mem_singleton ξ)
  have hxD : h.base ξ ∈ (D.support : Set X) :=
    Scheme.IdealSheafData.mem_support_comap.mp (hCsub hξC)
  have hxN : h.base ξ ∈ (N.support : Set X) :=
    Scheme.IdealSheafData.mem_support_comap.mp (hCN hξC)
  refine hN D hD (closure ({h.base ξ} : Set X)) isIrreducible_singleton.closure
    (closure_minimal (Set.singleton_subset_iff.mpr hxD) D.support.isClosed) ?_
    (closure_minimal (Set.singleton_subset_iff.mpr hxN) N.support.isClosed)
  intro C'' hC'' hC''sub hsub
  obtain ⟨η, hη⟩ := QuasiSober.sober hC''.closure isClosed_closure
  have hηmem : η ∈ closure C'' := by
    rw [← hη]
    exact subset_closure (Set.mem_singleton η)
  have hηD : η ∈ (D.support : Set X) :=
    closure_minimal hC''sub D.support.isClosed hηmem
  have hηspec : η ⤳ h.base ξ := by
    refine specializes_iff_mem_closure.mpr ?_
    rw [hη]
    exact subset_closure (hsub (subset_closure (Set.mem_singleton _)))
  obtain ⟨ξ', hξ'1, hξ'2⟩ := hg hηspec
  have hξ'2' : h.base ξ' = η := hξ'2
  have hξ'D : ξ' ∈ ((D.comap h).support : Set Y) := by
    refine Scheme.IdealSheafData.mem_support_comap.mpr ?_
    rw [hξ'2']
    exact hηD
  have hclos : closure ({ξ'} : Set Y) ⊆ ((D.comap h).support : Set Y) :=
    closure_minimal (Set.singleton_subset_iff.mpr hξ'D) (D.comap h).support.isClosed
  have hCsubξ' : C ⊆ closure ({ξ'} : Set Y) := by
    rw [← hξ]
    exact closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξ'1)) isClosed_closure
  have hclosure : closure ({ξ'} : Set Y) ⊆ C :=
    hCmax (closure ({ξ'} : Set Y)) isIrreducible_singleton.closure hclos hCsubξ'
  have hξ'C : ξ' ∈ C := hclosure (subset_closure (Set.mem_singleton _))
  have hspec : ξ ⤳ ξ' := by
    refine specializes_iff_mem_closure.mpr ?_
    rw [hξ]
    exact hξ'C
  have hspec2 : h.base ξ ⤳ h.base ξ' := hspec.map h.continuous
  have hηclos : η ∈ closure ({h.base ξ} : Set X) := by
    rw [← hξ'2']
    exact specializes_iff_mem_closure.mp hspec2
  intro z hz
  have hzc : z ∈ closure C'' := subset_closure hz
  rw [← hη] at hzc
  exact closure_minimal (Set.singleton_subset_iff.mpr hηclos) isClosed_closure hzc
end FunctorialResolution.EmbeddedResolution
