-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_etaleChart_on_open_of_hasStrictNormalCrossingsWith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:56.702873+00:00
-- url     : https://prove2.me/submissions/487138f4-4676-423a-aad4-5f149614d0ff

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_pullbackOpenImmersion_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_comap_preimage_eq_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_image_subset_of_image_inter_subset
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordIdeal_eq_comap_coordSubspaceIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_restrictToSubscheme_coordIdeal_singleton
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_top_of_le
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_comap_subscheme__eq_top_6abe0cb72e4b
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem mem_support_iff_forall_notMem_basicOpen {X : Scheme.{u}} (I : X.IdealSheafData)
    {x : ↥X} {U : X.Opens} (hU : IsAffineOpen U) (hx : x ∈ U) :
    x ∈ I.support ↔ ∀ f ∈ I.ideal ⟨U, hU⟩, x ∉ X.basicOpen f := by
  have h0 : x ∈ I.support ↔
      x ∈ X.zeroLocus (↑(I.ideal ⟨U, hU⟩) : Set Γ(X, U)) :=
    Scheme.IdealSheafData.mem_support_iff_of_mem hx
  rw [h0, Scheme.mem_zeroLocus_iff]
  exact Iff.rfl
private theorem subschemeι_base_mem_support_of_subscheme {W : Scheme.{u}} (Z : W.IdealSheafData)
    (z : ↥Z.subscheme) : Z.subschemeι.base z ∈ Z.support := by
  have h : Z.subschemeι.base z ∈ Set.range Z.subschemeι.base := ⟨z, rfl⟩
  rwa [Scheme.IdealSheafData.range_subschemeι] at h
private theorem complInv_def (m : ℕ) (S : Finset (Fin m)) (t : Fin m) :
    complOrderEmbInv m S t =
      if h : t ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S h)) :=
  rfl
private theorem complInv_eq_some_iff (m : ℕ) (S : Finset (Fin m)) {t : Fin m}
    {j : Fin (m - S.card)} : complOrderEmbInv m S t = some j ↔ complOrderEmb m S j = t := by
  constructor
  · intro h
    by_cases ht : t ∈ S
    · rw [complInv_def, dif_pos ht] at h
      simp at h
    · rw [complInv_def, dif_neg ht] at h
      have hj : Classical.choose (exists_complOrderEmb_eq m S ht) = j := Option.some.inj h
      have hspec := Classical.choose_spec (exists_complOrderEmb_eq m S ht)
      rw [hj] at hspec
      exact hspec
  · intro h
    have ht : t ∉ S := by
      rw [← h]
      exact complOrderEmb_notMem m S j
    rw [complInv_def, dif_neg ht]
    have hspec := Classical.choose_spec (exists_complOrderEmb_eq m S ht)
    have heq : Classical.choose (exists_complOrderEmb_eq m S ht) = j :=
      (complOrderEmb m S).injective (by rw [hspec, h])
    rw [heq]
private theorem eq_some_complOrderEmb_of_bind_complInv_eq_some (m : ℕ) (S : Finset (Fin m)) (o : Option (Fin m))
    (j : Fin (m - S.card)) (h : o.bind (complOrderEmbInv m S) = some j) :
    o = some (complOrderEmb m S j) := by
  cases o with
  | none => simp at h
  | some t =>
    have h' : complOrderEmbInv m S t = some j := h
    rw [(complInv_eq_some_iff m S).mp h']
private theorem eq_none_of_bind_complInv_eq_none (m : ℕ) (S : Finset (Fin m)) (o : Option (Fin m))
    (hnot : ∀ t, o = some t → t ∉ S) (h : o.bind (complOrderEmbInv m S) = none) : o = none := by
  cases o with
  | none => rfl
  | some t =>
    exfalso
    have h' : complOrderEmbInv m S t = none := h
    rw [complInv_def, dif_neg (hnot t rfl)] at h'
    simp at h'
section
variable {Y Y' : Scheme.{u}} {k : Type u} [Field k] {p : Y ⟶ Spec (CommRingCat.of k)}
  {V : Y.Opens} {n : ℕ}
private theorem restrictIdeal_comap_eq_coordIdeal_pullbackOpenImmersion (c : EtaleChart p V n)
    (f : Y' ⟶ Y) [IsOpenImmersion f] (D : Y.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal D V = c.coordIdeal S) :
    restrictIdeal (D.comap f) (f ⁻¹ᵁ V) = (c.pullbackOpenImmersion f).coordIdeal S := by
  have h1 : (c.pullbackOpenImmersion f).coordIdeal S
      = (c.coordIdeal S).comap (morphismRestrict f V) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal,
      EtaleChart.pullbackOpenImmersion_map, Scheme.IdealSheafData.comap_comp]
  rw [h1, ← h, restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
end
section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
end
section
variable {W : Scheme.{u}} {k : Type u} [Field k]
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {W : Scheme.{u}} {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (q : W ⟶ Spec (CommRingCat.of k))
    (E : List W.IdealSheafData) (Z : W.IdealSheafData) (hZ : HasStrictNormalCrossingsWith q Z E)
    (T : Z.subscheme.Opens)
    (hcomp : ∀ D ∈ E, ∀ C ∈ irreducibleComponents ↥T.toScheme,
      ¬ ((T.ι ≫ Z.subschemeι).base '' C ⊆ (D.support : Set ↥W)))
    (y : ↥T.toScheme) :
    ∃ (U : T.toScheme.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (n : ℕ)
      (c : EtaleChart (T.ι ≫ (Z.subschemeι ≫ q)) U n) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ hi : i < E.length,
        (γ i = none → restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = ⊤) ∧
          ∀ j, γ i = some j →
            restrictIdeal ((E[i]'hi).comap (T.ι ≫ Z.subschemeι)) U = c.coordIdeal {j}) ∧
      (∀ i i', i < E.length → i' < E.length → ∀ j, γ i = some j → γ i' = some j → i = i') := by
  classical
  have hbase : ∀ z : ↥T.toScheme,
      (T.ι ≫ Z.subschemeι).base z = Z.subschemeι.base (T.ι.base z) := fun _ => rfl
  have hcont : Continuous fun z : ↥T.toScheme => (T.ι ≫ Z.subschemeι).base z :=
    (T.ι ≫ Z.subschemeι).base.hom.continuous
  have hw : Z.subschemeι.base (T.ι.base y) ∈ Z.support := subschemeι_base_mem_support_of_subscheme Z _
  obtain ⟨U, hwU, m, c, a, S, hainj, hanone, hasome, hZU⟩ := hZ.exists_etaleChart hw
  obtain ⟨U₀, hU₀aff, hwU₀, hU₀le⟩ := exists_isAffineOpen_mem_and_subset hwU
  have hZU₀ : restrictIdeal Z U₀ = (c.restrict hU₀le).coordIdeal S :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hU₀le c Z S hZU
  have hE₀none : ∀ (i : ℕ) (hi : i < E.length), a i = none →
      restrictIdeal (E[i]'hi) U₀ = ⊤ := fun i hi h =>
    restrictIdeal_eq_top_of_le _ hU₀le (hanone i hi h)
  have hE₀some : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t →
      restrictIdeal (E[i]'hi) U₀ = (c.restrict hU₀le).coordIdeal {t} := fun i hi t h =>
    restrictIdeal_eq_restrict_coordIdeal_of_le hU₀le c _ _ (hasome i hi t h)
  have hnotS : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t → t ∉ S := by
    intro i hi t hat htS
    have hEle : (E[i]'hi).ideal ⟨U₀, hU₀aff⟩ ≤ Z.ideal ⟨U₀, hU₀aff⟩ := by
      rw [(c.restrict hU₀le).ideal_eq_span_coord hU₀aff _ _ (hE₀some i hi t hat),
        (c.restrict hU₀le).ideal_eq_span_coord hU₀aff _ _ hZU₀,
        Finset.coe_singleton, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span ⟨t, Finset.mem_coe.mpr htS, rfl⟩
    refine hcomp (E[i]'hi) (List.getElem_mem hi) (irreducibleComponent y)
      (irreducibleComponent_mem_irreducibleComponents y) ?_
    refine image_subset_of_image_inter_subset isIrreducible_irreducibleComponent
      (U₀.2.preimage hcont) ⟨y, mem_irreducibleComponent, ?_⟩ hcont
      (E[i]'hi).support.2 ?_
    · show (T.ι ≫ Z.subschemeι).base y ∈ (U₀ : Set ↥W)
      rw [hbase y]
      exact hwU₀
    · rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
      have hzU₀ : (T.ι ≫ Z.subschemeι).base z ∈ U₀ := hz
      have hzZ : (T.ι ≫ Z.subschemeι).base z ∈ Z.support := by
        rw [hbase z]
        exact subschemeι_base_mem_support_of_subscheme Z _
      exact (mem_support_iff_forall_notMem_basicOpen _ hU₀aff hzU₀).mpr
        (fun f hf => (mem_support_iff_forall_notMem_basicOpen Z hU₀aff hzU₀).mp hzZ f (hEle hf))
  have hyV : y ∈ T.ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U₀) := hwU₀
  obtain ⟨U₁, hU₁aff, hyU₁, hU₁le⟩ := exists_isAffineOpen_mem_and_subset hyV
  set d := (c.restrict hU₀le).restrictToSubscheme hU₀aff Z S hZU₀ with hd
  set d' := d.pullbackOpenImmersion T.ι with hd'
  refine ⟨U₁, hU₁aff, hyU₁, m - S.card, d'.restrict hU₁le,
    fun i => (a i).bind (complOrderEmbInv m S), ?_, ?_⟩
  · intro i hi
    constructor
    · intro hnone
      have hnone' : (a i).bind (complOrderEmbInv m S) = none := hnone
      have ha : a i = none :=
        eq_none_of_bind_complInv_eq_none m S (a i) (fun t ht => hnotS i hi t ht) hnone'
      have h1 := hE₀none i hi ha
      have h2 : restrictIdeal ((E[i]'hi).comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U₀) = ⊤ :=
        restrictIdeal_comap_subschemeι_eq_top Z U₀ _ h1
      have h3 : restrictIdeal (((E[i]'hi).comap Z.subschemeι).comap T.ι)
          (T.ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U₀)) = ⊤ :=
        restrictIdeal_comap_preimage_eq_top T.ι _ _ h2
      have h4 := restrictIdeal_eq_top_of_le _ hU₁le h3
      rw [Scheme.IdealSheafData.comap_comp]
      exact h4
    · intro j hj
      have hj' : (a i).bind (complOrderEmbInv m S) = some j := hj
      have ha : a i = some (complOrderEmb m S j) := eq_some_complOrderEmb_of_bind_complInv_eq_some m S (a i) j hj'
      have h1 := hE₀some i hi _ ha
      have h2 : restrictIdeal ((E[i]'hi).comap Z.subschemeι) (Z.subschemeι ⁻¹ᵁ U₀)
          = d.coordIdeal {j} :=
        (c.restrict hU₀le).restrictToSubscheme_coordIdeal_singleton hU₀aff Z S hZU₀ j _ h1
      have h3 : restrictIdeal (((E[i]'hi).comap Z.subschemeι).comap T.ι)
          (T.ι ⁻¹ᵁ (Z.subschemeι ⁻¹ᵁ U₀)) = d'.coordIdeal {j} :=
        restrictIdeal_comap_eq_coordIdeal_pullbackOpenImmersion d T.ι _ _ h2
      have h4 := restrictIdeal_eq_restrict_coordIdeal_of_le hU₁le d' _ _ h3
      rw [Scheme.IdealSheafData.comap_comp]
      exact h4
  · intro i i' hi hi' j hj hj'
    have hja : (a i).bind (complOrderEmbInv m S) = some j := hj
    have hjb : (a i').bind (complOrderEmbInv m S) = some j := hj'
    exact hainj i hi i' hi' (complOrderEmb m S j) (eq_some_complOrderEmb_of_bind_complInv_eq_some m S (a i) j hja)
      (eq_some_complOrderEmb_of_bind_complInv_eq_some m S (a i') j hjb)
end FunctorialResolution.EmbeddedResolution
