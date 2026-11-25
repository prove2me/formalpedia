-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_ker_cons_of_hasLocalCoordsOnSmoothHypersurface
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:27:04.176455+00:00
-- url     : https://prove2.me/submissions/d4aa4908-dbc5-45e5-8a3b-e7a54a7e37a1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_le_ker_comp_subscheme__0da5f0ebbe52
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_comp_subscheme__ideal_eq_span_coord_17965e032dc1
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_ideal_top
import Theorems.Thm_AlgebraicGeometry_Scheme_presheaf_map_eq_of_parallel
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordIdeal_eq_comap_coordSubspaceIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordSubspaceIdeal_eq_ofIdealTop_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_hasStrictNormalCrossingsWith_of_forall_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_of_le_of_eq
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {P : Scheme.{u}}
variable {k : Type u} [Field k]
end
section
variable {X : Scheme.{u}} {k : Type u} [Field k]
end
section
variable {P : Scheme.{u}} {k : Type u} [Field k]
private theorem comp_presheaf_map_comp_map {X₁ : Scheme.{u}} {R : CommRingCat.{u}}
    {A B C : (X₁.Opens)ᵒᵖ} (h : R ⟶ X₁.presheaf.obj A) (g₁ : A ⟶ B) (g₂ : B ⟶ C) (g₃ : A ⟶ C) :
    (h ≫ X₁.presheaf.map g₁) ≫ X₁.presheaf.map g₂ = h ≫ X₁.presheaf.map g₃ := by
  rw [Category.assoc, ← Functor.map_comp, X₁.presheaf_map_eq_of_parallel (g₁ ≫ g₂) g₃]
private theorem appLE_eq_appLE_comp_presheaf_map {X₁ Y₁ : Scheme.{u}} (f : X₁ ⟶ Y₁) (U : Y₁.Opens)
    {A B : X₁.Opens} (e : A ≤ f ⁻¹ᵁ U) (e' : B ≤ f ⁻¹ᵁ U) (hAB : A ≤ B) :
    f.appLE U A e = f.appLE U B e' ≫ X₁.presheaf.map (homOfLE hAB).op := by
  have h1 : f.appLE U A e = f.app U ≫ X₁.presheaf.map (homOfLE e).op := rfl
  have h2 : f.appLE U B e' = f.app U ≫ X₁.presheaf.map (homOfLE e').op := rfl
  rw [h1, h2]
  exact (comp_presheaf_map_comp_map (f.app U) (homOfLE e').op (homOfLE hAB).op (homOfLE e).op).symm
private theorem ι_appLE_self_top_eq_topIso_inv {X₁ : Scheme.{u}} (V : X₁.Opens)
    (e : (⊤ : (V.toScheme).Opens) ≤ V.ι ⁻¹ᵁ V) :
    V.ι.appLE V ⊤ e = V.topIso.inv := by
  simp
  exact X₁.presheaf_map_eq_of_parallel _ _
private theorem ι_appLE_apply_topIso_hom {X₁ Y₁ : Scheme.{u}} (V : X₁.Opens)
    (g : V.toScheme ⟶ Y₁) {W : V.toScheme.Opens} (e1 : W ≤ V.ι ⁻¹ᵁ V)
    (e2 : W ≤ g ⁻¹ᵁ (⊤ : Y₁.Opens)) (x : Γ(Y₁, ⊤)) :
    (V.ι.appLE V W e1).hom (V.topIso.hom.hom (g.appTop.hom x))
      = (g.appLE ⊤ W e2).hom x := by
  have htop : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by
    intro y _
    exact y.2
  have ha : V.ι.appLE V W e1
      = V.topIso.inv ≫ V.toScheme.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    rw [appLE_eq_appLE_comp_presheaf_map V.ι V e1 htop le_top, ι_appLE_self_top_eq_topIso_inv V htop]
  have hb : g.appLE (⊤ : Y₁.Opens) W e2
      = g.appTop ≫ V.toScheme.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    have h1 : g.appLE (⊤ : Y₁.Opens) W e2
        = g.appTop ≫ V.toScheme.presheaf.map (homOfLE e2).op := rfl
    rw [h1]
    exact congrArg (fun z => g.appTop ≫ z) (V.toScheme.presheaf_map_eq_of_parallel _ _)
  rw [ha, hb]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [Iso.hom_inv_id_apply]
private theorem ofIdealTop_ideal_top {Y : Scheme.{u}} [IsAffine Y] (J : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Y⟩ = J := by
  simp
private theorem ι_appLE_coord {X₁ : Scheme.{u}} {K : Type u} [Field K]
    {q : X₁ ⟶ Spec (CommRingCat.of K)} {U : X₁.Opens} {m : ℕ} (c : EtaleChart q U m)
    {W : U.toScheme.Opens} (e1 : W ≤ U.ι ⁻¹ᵁ U)
    (e2 : W ≤ c.map ⁻¹ᵁ (⊤ : (affineSpaceFin K m).Opens)) (j : Fin m) :
    (U.ι.appLE U W e1).hom (c.coord j)
      = (c.map.appLE ⊤ W e2).hom
          (AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up j : ULift.{u} (Fin m))) := by
  rw [EtaleChart.coord_def]
  exact ι_appLE_apply_topIso_hom U c.map e1 e2 _
private theorem restrictIdeal_eq_coordIdeal_of_isAffineOpen_ideal_eq_span {X₁ : Scheme.{u}} {K : Type u}
    [Field K] {q : X₁ ⟶ Spec (CommRingCat.of K)} {U : X₁.Opens} {m : ℕ}
    (c : EtaleChart q U m) (hU : IsAffineOpen U) (I : X₁.IdealSheafData) (S : Finset (Fin m))
    (h : I.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m)))) :
    restrictIdeal I U = c.coordIdeal S := by
  have hAaff : IsAffine (affineSpaceFin K m) := inferInstance
  have hcoord : (coordSubspaceIdeal K m S).ideal ⟨⊤, isAffineOpen_top (affineSpaceFin K m)⟩
      = Ideal.span ((fun i : Fin m =>
          AffineSpace.coord (Spec (CommRingCat.of K)) (ULift.up i)) '' (S : Set (Fin m))) := by
    rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
    exact ofIdealTop_ideal_top _
  refine Scheme.IdealSheafData.ext (funext ?_)
  intro W
  have htop : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := by
    intro y _
    exact y.2
  have eW : (W.1 : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := le_trans le_top htop
  have eW' : (W.1 : U.toScheme.Opens) ≤ c.map ⁻¹ᵁ (⊤ : (affineSpaceFin K m).Opens) := by
    intro y _
    trivial
  show (I.comap U.ι).ideal W = ((coordSubspaceIdeal K m S).comap c.map).ideal W
  rw [I.comap_ideal_eq_map_appLE U.ι ⟨U, hU⟩ W eW,
    (coordSubspaceIdeal K m S).comap_ideal_eq_map_appLE c.map
      ⟨⊤, isAffineOpen_top (affineSpaceFin K m)⟩ W eW',
    h, hcoord, Ideal.map_span, Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
  refine congrArg Ideal.span (Set.image_congr fun j _ => ?_)
  exact ι_appLE_coord c eW eW' j
private theorem ideal_ne_top_of_mem_support {Y : Scheme.{u}} (I : Y.IdealSheafData) {V : Y.Opens}
    (hV : IsAffineOpen V) {x : Y} (hxV : x ∈ V) (hx : x ∈ I.support) :
    I.ideal ⟨V, hV⟩ ≠ ⊤ := by
  obtain ⟨y, hy⟩ : ∃ y : I.subscheme, I.subschemeι.base y = x := by
    have hxs : x ∈ (I.support : Set Y) := hx
    have hxr : x ∈ Set.range I.subschemeι.base := by simpa using hxs
    exact hxr
  have hyV : y ∈ I.subschemeι ⁻¹ᵁ V := by
    show I.subschemeι.base y ∈ V
    rw [hy]
    exact hxV
  have hnt : Nontrivial Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) :=
    RingHom.domain_nontrivial (I.subscheme.presheaf.germ (I.subschemeι ⁻¹ᵁ V) y hyV).hom
  intro htop
  have hker : RingHom.ker (I.subschemeι.app V).hom = I.ideal ⟨V, hV⟩ :=
    Scheme.IdealSheafData.ker_subschemeι_app I ⟨V, hV⟩
  have hmem1 : (1 : Γ(Y, V)) ∈ RingHom.ker (I.subschemeι.app V).hom := by
    rw [hker, htop]
    exact Submodule.mem_top
  have hzero : (1 : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) = 0 := by
    have h' := RingHom.mem_ker.mp hmem1
    rwa [map_one] at h'
  exact one_ne_zero hzero
private theorem ideal_eq_top_of_restrictIdeal_eq_top {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (h : restrictIdeal I V = ⊤) :
    I.ideal ⟨V, hV⟩ = ⊤ := by
  have hVaff : IsAffine V.toScheme := hV
  have htop : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by
    intro y _
    exact y.2
  have key := I.comap_ideal_eq_map_appLE V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ htop
  rw [ι_appLE_self_top_eq_topIso_inv V htop] at key
  have h' : I.comap V.ι = ⊤ := h
  rw [h'] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  rw [Ideal.eq_top_iff_one]
  have hone : (1 : Γ(V.toScheme, ⊤)) ∈ Ideal.map V.topIso.inv.hom (I.ideal ⟨V, hV⟩) := by
    rw [← key]
    exact Submodule.mem_top
  have hsurj : Function.Surjective V.topIso.inv.hom :=
    V.topIso.symm.commRingCatIsoToRingEquiv.surjective
  have hinj : Function.Injective V.topIso.inv.hom :=
    V.topIso.symm.commRingCatIsoToRingEquiv.injective
  obtain ⟨a, haI, hfa⟩ :=
    (Ideal.mem_map_iff_of_surjective _ hsurj).mp hone
  have ha1 : a = 1 := hinj (by rw [hfa, map_one])
  exact ha1 ▸ haI
private theorem restrictIdeal_eq_top_of_le_of_eq_top {Y : Scheme.{u}} (I : Y.IdealSheafData) {U V : Y.Opens}
    (hVU : V ≤ U) (h : restrictIdeal I U = ⊤) : restrictIdeal I V = ⊤ := by
  have e1 : I.comap V.ι = (I.comap U.ι).comap (Y.homOfLE hVU) := by
    rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
  have h' : I.comap U.ι = ⊤ := h
  show I.comap V.ι = ⊤
  rw [e1, h']
  simp
private theorem restrictIdeal_eq_coordIdeal_restrict {X₁ : Scheme.{u}} {K : Type u} [Field K]
    {q : X₁ ⟶ Spec (CommRingCat.of K)} {U V : X₁.Opens} (hVU : V ≤ U) {m : ℕ}
    (c : EtaleChart q U m) (I : X₁.IdealSheafData) (S : Finset (Fin m))
    (h : restrictIdeal I U = c.coordIdeal S) :
    restrictIdeal I V = (c.restrict hVU).coordIdeal S := by
  have h' : I.comap U.ι = (coordSubspaceIdeal K m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map,
    Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
    Scheme.homOfLE_ι]
private theorem mem_span_X_of_mul_X_mem {σ : Type u} {K : Type u} [Field K]
    {j s : σ} (hjs : j ≠ s) (r : MvPolynomial σ K)
    (hr : MvPolynomial.X s * r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)}) :
    r ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)} := by
  classical
  obtain ⟨ψ, hψC, hψXj, hψXi⟩ : ∃ ψ : MvPolynomial σ K →+* MvPolynomial σ K,
      (∀ a : K, ψ (MvPolynomial.C a) = MvPolynomial.C a) ∧
        ψ (MvPolynomial.X j) = 0 ∧
        ∀ i : σ, i ≠ j → ψ (MvPolynomial.X i) = MvPolynomial.X i := by
    refine ⟨MvPolynomial.eval₂Hom (MvPolynomial.C : K →+* MvPolynomial σ K)
        (fun i : σ => if i = j then (0 : MvPolynomial σ K) else MvPolynomial.X i), ?_, ?_, ?_⟩
    · intro a
      simp
    · simp
    · intro i hi
      simp [hi]
  have hXjmem : (MvPolynomial.X j : MvPolynomial σ K)
      ∈ Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)} := Ideal.mem_span_singleton_self _
  have key : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)})).comp ψ
      = Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)}) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, hψC]
    · intro i
      rw [RingHom.comp_apply]
      by_cases h : i = j
      · subst h
        rw [hψXj, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr hXjmem).symm
      · rw [hψXi i h]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hr
  have h0 : ψ (MvPolynomial.X s * r) = 0 := by
    rw [ht, map_mul, hψXj, zero_mul]
  rw [map_mul, hψXi s (Ne.symm hjs)] at h0
  have hXs : (MvPolynomial.X s : MvPolynomial σ K) ≠ 0 := MvPolynomial.X_ne_zero _
  have hψr : ψ r = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hXs
    · exact h
  have h3 := DFunLike.congr_fun key r
  rw [RingHom.comp_apply, hψr, map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3.symm
private theorem quotient_span_X_mul_X_cancel {σ : Type u} {K : Type u} [Field K] {j s : σ} (hjs : j ≠ s)
    (a b : MvPolynomial σ K ⧸ Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)})
    (h : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)}))
            (MvPolynomial.X s) * a
        = (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X j : MvPolynomial σ K)}))
            (MvPolynomial.X s) * b) : a = b := by
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at h
  exact Ideal.Quotient.eq.mpr (mem_span_X_of_mul_X_mem hjs (a' - b') h)
private theorem mem_map_of_mul_mem_of_etale {Pr A : Type u} [CommRing Pr] [CommRing A]
    {f : Pr →+* A} (hf : f.Etale) (I : Ideal Pr) (w : Pr)
    (hw : ∀ a b : Pr ⧸ I,
      (Ideal.Quotient.mk I) w * a = (Ideal.Quotient.mk I) w * b → a = b)
    (x : A) (hx : f w * x ∈ Ideal.map f I) : x ∈ Ideal.map f I := by
  have hg : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale :=
    etale_quotientMap hf I
  have hy : (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)
        ((Ideal.Quotient.mk I) w) * (Ideal.Quotient.mk (Ideal.map f I)) x = 0 := by
    rw [Ideal.quotientMap_mk, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let algInst : Algebra (Pr ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have instEt : Algebra.Etale (Pr ⧸ I) (A ⧸ Ideal.map f I) := hg
  have instFlat : Module.Flat (Pr ⧸ I) (A ⧸ Ideal.map f I) := inferInstance
  have hreg : IsSMulRegular (Pr ⧸ I) ((Ideal.Quotient.mk I) w) := fun a b h => hw a b h
  have hregA : IsSMulRegular (A ⧸ Ideal.map f I) ((Ideal.Quotient.mk I) w) := hreg.of_flat
  have hsmul : (Ideal.Quotient.mk I) w • (Ideal.Quotient.mk (Ideal.map f I)) x
      = (Ideal.Quotient.mk I) w • (0 : A ⧸ Ideal.map f I) := by
    rw [smul_zero]
    exact hy
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hregA hsmul)
private theorem span_coord_eq_top_of_mem_span {X₁ : Scheme.{u}} {K : Type u} [Field K]
    {q : X₁ ⟶ Spec (CommRingCat.of K)} {V : X₁.Opens} (hV : IsAffineOpen V) {m : ℕ}
    (c : EtaleChart q V m) {j s : Fin m} (hjs : j ≠ s)
    (hmem : c.coord s ∈ Ideal.span {c.coord j}) :
    Ideal.span {c.coord j} = (⊤ : Ideal Γ(X₁, V)) := by
  classical
  have hmapspan : Ideal.map c.coordRingHom
      (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)})
      = Ideal.span {c.coord j} := by
    rw [Ideal.map_span, Set.image_singleton, c.coordRingHom_X]
  have hju : (ULift.up j : ULift.{u} (Fin m)) ≠ ULift.up s := by
    intro h
    exact hjs (congrArg ULift.down h)
  have hu : ∀ a b : MvPolynomial (ULift.{u} (Fin m)) K ⧸
        Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)},
      (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)}))
          (MvPolynomial.X (ULift.up s)) * a
        = (Ideal.Quotient.mk
          (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)}))
          (MvPolynomial.X (ULift.up s)) * b → a = b :=
    fun a b h => quotient_span_X_mul_X_cancel hju a b h
  have hx' : c.coordRingHom (MvPolynomial.X (ULift.up s)) * 1
      ∈ Ideal.map c.coordRingHom
        (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)}) := by
    rw [hmapspan, c.coordRingHom_X, mul_one]
    exact hmem
  have hfin := mem_map_of_mul_mem_of_etale (c.coordRingHom_etale hV)
    (Ideal.span {(MvPolynomial.X (ULift.up j) : MvPolynomial (ULift.{u} (Fin m)) K)})
    (MvPolynomial.X (ULift.up s)) hu 1 hx'
  rw [hmapspan] at hfin
  exact (Ideal.eq_top_iff_one _).mpr hfin
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}} {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [CharZero k] (p : P ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] (H : P.IdealSheafData) (N : List P.IdealSheafData)
    (Z : H.subscheme.IdealSheafData)
    (hN : InStrictNormalCrossingPosition p (H :: N))
    (_hZ : HasStrictNormalCrossingsWith (H.subschemeι ≫ p) Z (N.map fun D => D.comap H.subschemeι))
    (hdata : HasLocalCoordsOnSmoothHypersurface p H N Z) :
    HasStrictNormalCrossingsWith p (Z.subschemeι ≫ H.subschemeι).ker (H :: N) := by
  classical
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hU, hxU, n, c, j₀, lab, S, h1, h2, h3, h4, h5⟩ := hdata x hx
  obtain ⟨-, hNpos⟩ := (inStrictNormalCrossingPosition_iff p (H :: N)).mp hN
  have hclash : ∀ i : ℕ, i < N.length → lab i ≠ some j₀ := by
    intro i hi hlabi
    obtain ⟨U', hxU', m', c', a', hinj', hnone', hsome'⟩ := (hNpos x).exists_etaleChart
    obtain ⟨V, hVb, hxV, hVle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens
        (show x ∈ U ⊓ U' from ⟨hxU, hxU'⟩)
    have hV : IsAffineOpen V := hVb
    have hVU : V ≤ U := le_trans hVle inf_le_left
    have hVU' : V ≤ U' := le_trans hVle inf_le_right
    have hEqU : restrictIdeal (N[i]'hi) U = restrictIdeal H U := by
      rw [h3 i hi j₀ hlabi, h1]
    have hEqV : restrictIdeal (N[i]'hi) V = restrictIdeal H V :=
      restrictIdeal_eq_of_le_of_eq hVU hEqU
    have hKne : (Z.subschemeι ≫ H.subschemeι).ker.ideal ⟨V, hV⟩ ≠ ⊤ :=
      ideal_ne_top_of_mem_support _ hV hxV hx
    have hproper : H.ideal ⟨V, hV⟩ ≠ ⊤ := by
      intro htop
      have hle := le_ker_comp_subschemeι H Z ⟨V, hV⟩
      rw [htop] at hle
      exact hKne (top_le_iff.mp hle)
    have hlen0 : 0 < (H :: N).length := by simp
    have hleni : i + 1 < (H :: N).length := by simpa using hi
    cases hop : a' 0 with
    | none =>
      have hHtop : restrictIdeal H U' = ⊤ := by simpa using hnone' 0 hlen0 hop
      exact hproper (ideal_eq_top_of_restrictIdeal_eq_top H hV
        (restrictIdeal_eq_top_of_le_of_eq_top H hVU' hHtop))
    | some t₀ =>
      cases hop1 : a' (i + 1) with
      | none =>
        have hNtop : restrictIdeal (N[i]'hi) U' = ⊤ := by
          simpa using hnone' (i + 1) hleni hop1
        have hVtop : restrictIdeal (N[i]'hi) V = ⊤ := restrictIdeal_eq_top_of_le_of_eq_top _ hVU' hNtop
        rw [hEqV] at hVtop
        exact hproper (ideal_eq_top_of_restrictIdeal_eq_top H hV hVtop)
      | some t₁ =>
        have hne : t₀ ≠ t₁ := by
          intro hteq
          have h00 := hinj' 0 hlen0 (i + 1) hleni t₀ hop (by rw [hop1, hteq])
          exact absurd h00 (by omega)
        have hHU' : restrictIdeal H U' = c'.coordIdeal {t₀} := by
          simpa using hsome' 0 hlen0 t₀ hop
        have hNU' : restrictIdeal (N[i]'hi) U' = c'.coordIdeal {t₁} := by
          simpa using hsome' (i + 1) hleni t₁ hop1
        have hHV1 : restrictIdeal H V = (c'.restrict hVU').coordIdeal {t₀} :=
          restrictIdeal_eq_coordIdeal_restrict hVU' c' H {t₀} hHU'
        have hHV2 : restrictIdeal H V = (c'.restrict hVU').coordIdeal {t₁} := by
          rw [← hEqV]
          exact restrictIdeal_eq_coordIdeal_restrict hVU' c' (N[i]'hi) {t₁} hNU'
        have hA : H.ideal ⟨V, hV⟩ = Ideal.span {(c'.restrict hVU').coord t₀} := by
          simpa using (c'.restrict hVU').ideal_eq_span_coord hV H {t₀} hHV1
        have hB : H.ideal ⟨V, hV⟩ = Ideal.span {(c'.restrict hVU').coord t₁} := by
          simpa using (c'.restrict hVU').ideal_eq_span_coord hV H {t₁} hHV2
        have hmem : (c'.restrict hVU').coord t₁
            ∈ Ideal.span {(c'.restrict hVU').coord t₀} := by
          rw [← hA, hB]
          exact Ideal.mem_span_singleton_self _
        exact hproper (hA.trans (span_coord_eq_top_of_mem_span hV (c'.restrict hVU') hne hmem))
  obtain ⟨a, ha0, has⟩ : ∃ a : ℕ → Option (Fin n), a 0 = some j₀ ∧ ∀ i, a (i + 1) = lab i :=
    ⟨fun i => if i = 0 then some j₀ else lab (i - 1), if_pos rfl, fun i => by
      show (if i + 1 = 0 then some j₀ else lab (i + 1 - 1)) = lab i
      rw [if_neg (by omega : ¬ (i + 1 = 0)), Nat.add_sub_cancel]⟩
  refine ⟨U, hxU, n, c, a, insert j₀ S, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        have heq : j₀ = t := by
          rw [ha0] at hti
          exact Option.some.inj hti
        rw [has j'] at htj
        rw [← heq] at htj
        exact absurd htj (hclash j' (by simpa using hj))
    | succ i' =>
      cases j with
      | zero =>
        have heq : j₀ = t := by
          rw [ha0] at htj
          exact Option.some.inj htj
        rw [has i'] at hti
        rw [← heq] at hti
        exact absurd hti (hclash i' (by simpa using hi))
      | succ j' =>
        rw [has i'] at hti
        rw [has j'] at htj
        have hij := h4 i' j' (by simpa using hi) (by simpa using hj) t hti htj
        omega
  · intro i hi hn
    cases i with
    | zero =>
      rw [ha0] at hn
      exact absurd hn (by simp)
    | succ i' =>
      rw [has i'] at hn
      have hi' : i' < N.length := by simpa using hi
      simpa using h2 i' hi' hn
  · intro i hi t ht
    cases i with
    | zero =>
      have heq : j₀ = t := by
        rw [ha0] at ht
        exact Option.some.inj ht
      rw [← heq]
      simpa using h1
    | succ i' =>
      rw [has i'] at ht
      have hi' : i' < N.length := by simpa using hi
      simpa using h3 i' hi' t ht
  · exact restrictIdeal_eq_coordIdeal_of_isAffineOpen_ideal_eq_span c hU _ (insert j₀ S)
      (ker_comp_subschemeι_ideal_eq_span_coord p H Z hU c j₀ S h1 h5)
end FunctorialResolution.EmbeddedResolution
