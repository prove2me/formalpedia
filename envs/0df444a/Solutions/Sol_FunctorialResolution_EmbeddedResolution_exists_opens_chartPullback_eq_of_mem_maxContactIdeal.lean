-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_opens_chartPullback_eq_of_mem_maxContactIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:06.949332+00:00
-- url     : https://prove2.me/submissions/a10c8f1c-5950-4359-8ad8-4366a0683b02

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_StalkIdealSpreadOut
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactChartUniqueness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartsAgreeAt_of_coord_eq_of_germ_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordIdeal_eq_of_coord_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_comap_chartPullbackPoint_eq
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_fromSpecStalk_comp_subscheme__chartPullback_eq_edf95e69c754
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartPullback_comap_coordIdeal_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_opens_stalkIdeal_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_of_stalkIdeal_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
end
private theorem exists_preimage_eq_of_isClosedImmersion {Y Z : Scheme.{u}} (f : Z ⟶ Y) [IsClosedImmersion f]
    (W : Z.Opens) : ∃ V : Y.Opens, f ⁻¹ᵁ V = W := by
  have hind := (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding f).toIsEmbedding.toIsInducing
  obtain ⟨t, ht, hteq⟩ := hind.isOpen_iff.mp W.2
  exact ⟨⟨t, ht⟩, TopologicalSpace.Opens.ext hteq⟩
private theorem ι_comp_eq_of_le {Z Y : Scheme.{u}} {W₀ W' : Z.Opens} (hle : W₀ ≤ W')
    {f g : Z ⟶ Y} (hfg : W'.ι ≫ f = W'.ι ≫ g) : W₀.ι ≫ f = W₀.ι ≫ g := by
  rw [← Scheme.homOfLE_ι _ hle, Category.assoc, hfg, Category.assoc]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
    (hinv : IsMaxContactInvariant k p I m)
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (x : X) (hx : x ∈ U)
    (hmem₁ : c₁.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hmem₂ : c₂.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hsupp : x ∈ (maxContactIdeal k p I m).support)
    [IsLocallyNoetherian (chartPullback c₁ c₂)]
    [IsLocallyNoetherian ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme] :
    ∃ h : ChartsAgreeAt c₁ c₂ x hx,
      ∃ W : (chartPullback c₁ c₂).Opens, chartPullbackPoint c₁ c₂ x hx h ∈ W ∧
        (∀ y : ↥(chartPullback c₁ c₂), y ∈ W →
            stalkIdeal (I.comap (chartPullbackFst c₁ c₂)) y =
              stalkIdeal (I.comap (chartPullbackSnd c₁ c₂)) y) ∧
        restrictIdeal (I.comap (chartPullbackFst c₁ c₂)) W =
          restrictIdeal (I.comap (chartPullbackSnd c₁ c₂)) W ∧
        ((((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ W).ι ≫
              ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
                chartPullbackFst c₁ c₂ =
            (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ W).ι ≫
              ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
                chartPullbackSnd c₁ c₂) ∧
        ((c₁.coordIdeal {j}).comap (pullback.fst c₁.map c₂.map) =
          (c₂.coordIdeal {j}).comap (pullback.snd c₁.map c₂.map)) ∧
        ∀ S : Finset (Fin n), j ∉ S → c₁.coordIdeal S = c₂.coordIdeal S := by
  classical
  have hagree : ChartsAgreeAt c₁ c₂ x hx :=
    chartsAgreeAt_of_coord_eq_of_germ_mem c₁ c₂ j x hx hcoord hg₁ hg₂
  have hst : stalkIdeal (I.comap (chartPullbackFst c₁ c₂)) (chartPullbackPoint c₁ c₂ x hx hagree) =
      stalkIdeal (I.comap (chartPullbackSnd c₁ c₂)) (chartPullbackPoint c₁ c₂ x hx hagree) :=
    stalkIdeal_comap_chartPullbackPoint_eq k p I hm hinv hU c₁ c₂ j hcoord x hx hmem₁ hmem₂ hg₁ hg₂
      hagree
  obtain ⟨W₁, hW₁mem, hW₁⟩ :=
    exists_opens_stalkIdeal_eq (I.comap (chartPullbackFst c₁ c₂)) (I.comap (chartPullbackSnd c₁ c₂))
      (chartPullbackPoint c₁ c₂ x hx hagree) hst
  have hsupp' : chartPullbackPoint c₁ c₂ x hx hagree ∈
      ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).support := by
    have hz : (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ x hx hagree) ∈
        (maxContactIdeal k p I m).support := by
      rw [chartPullbackFst_base_chartPullbackPoint c₁ c₂ x hx hagree]
      exact hsupp
    rw [Scheme.IdealSheafData.support_comap]
    exact hz
  have hrange : chartPullbackPoint c₁ c₂ x hx hagree ∈
      Set.range (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι.base) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hsupp'
  obtain ⟨z, hz⟩ := hrange
  have hmor := fromSpecStalk_comp_subschemeι_chartPullback_eq k p I hm hinv hU c₁ c₂ j hcoord x hx
    hmem₁ hmem₂ hg₁ hg₂ hsupp hagree z hz
  obtain ⟨W', hzW', hW'⟩ :=
    AlgebraicGeometry.spread_out_unique_of_isGermInjective'
      (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫ chartPullbackFst c₁ c₂)
      (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫ chartPullbackSnd c₁ c₂)
      hmor
  obtain ⟨V, hV⟩ :=
    _root_.FunctorialResolution.EmbeddedResolution.exists_preimage_eq_of_isClosedImmersion ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι W'
  have hptV : chartPullbackPoint c₁ c₂ x hx hagree ∈ V := by
    have h1 : z ∈ ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ V := by
      rw [hV]
      exact hzW'
    have h2 : ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι.base z ∈ V := h1
    rw [hz] at h2
    exact h2
  have hstalk : ∀ y : ↥(chartPullback c₁ c₂), y ∈ W₁ ⊓ V →
      stalkIdeal (I.comap (chartPullbackFst c₁ c₂)) y =
        stalkIdeal (I.comap (chartPullbackSnd c₁ c₂)) y := fun y hy => hW₁ y hy.1
  have hle : (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ (W₁ ⊓ V))
      ≤ W' := by
    rw [← hV]
    intro w hw
    exact hw.2
  exact ⟨hagree, W₁ ⊓ V, ⟨hW₁mem, hptV⟩, hstalk,
    restrictIdeal_eq_of_stalkIdeal_eq _ _ (W₁ ⊓ V) hstalk,
    ι_comp_eq_of_le hle hW',
    chartPullback_comap_coordIdeal_eq c₁ c₂ {j},
    fun S hS => coordIdeal_eq_of_coord_eq hU c₁ c₂ S (by
      intro i hi
      refine hcoord i ?_
      rintro rfl
      exact hS hi)⟩
end FunctorialResolution.EmbeddedResolution
