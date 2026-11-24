-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_coordBlowupSubstMap_coordSubspaceIdeal_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:24.334685+00:00
-- url     : https://prove2.me/submissions/a50725c0-cb53-4f08-9e16-927f61c31301

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_singleton
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordBlowupSubstMap_appTop_coord_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordBlowupSubstMap_appTop_coord_self
import Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop_bf5846d67e16db07
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_eq_ofIdealTop_span_coord


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    (coordSubspaceIdeal k m S).comap (coordBlowupSubstMap k m S s) = coordSubspaceIdeal k m {s} := by
  have key : Ideal.map ((coordBlowupSubstMap k m S s).appTop.hom)
      (Ideal.span
        ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
          (S : Set (Fin m)))) =
      Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)} := by
    rw [Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro y ⟨z, ⟨i, hi, rfl⟩, rfl⟩
      have hiS : i ∈ S := Finset.mem_coe.mp hi
      show (coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ∈
          Ideal.span {AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)}
      by_cases h : i = s
      · have h2 : (coordBlowupSubstMap k m S s).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) =
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s) := by
          rw [h]
          exact coordBlowupSubstMap_appTop_coord_self k m S s
        rw [h2]
        exact Ideal.mem_span_singleton_self _
      · rw [coordBlowupSubstMap_appTop_coord_of_mem k m S s i hiS h]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hmem : (coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s)) ∈
          ((coordBlowupSubstMap k m S s).appTop.hom ''
            ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
              (S : Set (Fin m)))) :=
        Set.mem_image_of_mem _ (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hs))
      rw [coordBlowupSubstMap_appTop_coord_self k m S s] at hmem
      exact Ideal.subset_span hmem
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, Scheme.IdealSheafData.comap_ofIdealTop, key,
    coordSubspaceIdeal_singleton]
end FunctorialResolution.EmbeddedResolution
