-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_etaleChart_coord_mem_primeIdealOf_on_clopen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:56:07.35628+00:00
-- url     : https://prove2.me/submissions/328fd02b-5b40-40e8-8e88-22360888a2a1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart_coord_mem_primeIdealOf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def



set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {W : Scheme.{u}} {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (q : W ⟶ Spec (CommRingCat.of k)) [Smooth q]
    (E : List W.IdealSheafData) (_hE : InStrictNormalCrossingPosition q E) (Z : W.IdealSheafData)
    (hZ : HasStrictNormalCrossingsWith q Z E) (T : Z.subscheme.Opens)
    (_hTclosed : IsClosed (T : Set ↥Z.subscheme))
    (hcomp : ∀ D ∈ E, ∀ C ∈ irreducibleComponents ↥T.toScheme,
      ¬ ((T.ι ≫ Z.subschemeι).base '' C ⊆ (D.support : Set ↥W)))
    (y : ↥T.toScheme) :
    ∃ (U : T.toScheme.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (n : ℕ)
      (c : EtaleChart (T.ι ≫ (Z.subschemeι ≫ q)) U n) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ hi : i < E.length,
        (γ i = none → restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = ⊤) ∧
          ∀ j, γ i = some j →
            restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = c.coordIdeal {j}) ∧
      (∀ i i', i < E.length → i' < E.length → ∀ j, γ i = some j → γ i' = some j → i = i') ∧
      (∀ i, i < E.length → ∀ j, γ i = some j → c.coord j ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  classical
  obtain ⟨U, hU, hy, n, c, γ, hdesc, hinj⟩ :=
    exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith q E Z hZ T hcomp y
  have hlen : (E.map fun D : W.IdealSheafData => D.comap (T.ι ≫ Z.subschemeι)).length
      = E.length := by
    simp
  have hdesc' : ∀ i, ∀ hi : i < (E.map fun D : W.IdealSheafData =>
        D.comap (T.ι ≫ Z.subschemeι)).length,
      (γ i = none → restrictIdeal ((E.map fun D : W.IdealSheafData =>
          D.comap (T.ι ≫ Z.subschemeι))[i]'hi) U = ⊤) ∧
        ∀ j, γ i = some j → restrictIdeal ((E.map fun D : W.IdealSheafData =>
          D.comap (T.ι ≫ Z.subschemeι))[i]'hi) U = c.coordIdeal {j} := by
    intro i hi
    have hi' : i < E.length := by rwa [hlen] at hi
    obtain ⟨hA, hB⟩ := hdesc i hi'
    simp only [List.getElem_map]
    exact ⟨hA, hB⟩
  have hinj' : ∀ i i', i < (E.map fun D : W.IdealSheafData =>
      D.comap (T.ι ≫ Z.subschemeι)).length →
      i' < (E.map fun D : W.IdealSheafData => D.comap (T.ι ≫ Z.subschemeι)).length →
      ∀ j, γ i = some j → γ i' = some j → i = i' := by
    intro i i' hi hi' j h1 h2
    rw [hlen] at hi hi'
    exact hinj i i' hi hi' j h1 h2
  obtain ⟨U', hU', hy', n', c', γ', h1, h2, h3⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf
      (E.map fun D : W.IdealSheafData => D.comap (T.ι ≫ Z.subschemeι)) y U hU hy c γ
      hdesc' hinj'
  refine ⟨U', hU', hy', n', c', γ', ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < (E.map fun D : W.IdealSheafData =>
        D.comap (T.ι ≫ Z.subschemeι)).length := by
      rw [hlen]; exact hi
    obtain ⟨hA, hB⟩ := h1 i hi'
    simp only [List.getElem_map] at hA hB
    exact ⟨hA, hB⟩
  · intro i i' hi hi' j hj hj'
    exact h2 i i' (by rw [hlen]; exact hi) (by rw [hlen]; exact hi') j hj hj'
  · intro i hi j hj
    exact h3 i (by rw [hlen]; exact hi) j hj
end FunctorialResolution.EmbeddedResolution
