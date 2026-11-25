-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.embeddedPrincipalizationYieldsBlowups_of_discardedLocusIsOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:23:31.813381+00:00
-- url     : https://prove2.me/submissions/68a59121-e536-4071-a94f-d89c8ca627de

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_EmbeddedStrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_DiscardedLocus
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_noetherianSpace_strictTransform_of_ambientLevel
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_image_discardedLocus_subset_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_range_strictTransformMap_subset_discardedLocusClosureCompl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_exists_iso_discardedSubscheme_discardedLocusOpens
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_isReduced_strictTransform
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_isBlowupAlongIdealSheaf_transitionMap_of_coprodDesc
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_range_comp_base
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_of_comap_of_isOpenImmersion_cover
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_of_isIso
import Theorems.Thm_FunctorialResolution_Blowup_comap_eq_top_of_notMem_support
import Theorems.Thm_FunctorialResolution_Blowup_exists_iso_pullback_coprod_desc_left
import Theorems.Thm_FunctorialResolution_Blowup_exists_iso_pullback_coprod_desc_right
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_blowupSequence_tower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_centerOffDetached_eq
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_coe_discardedLocusClosure
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_coe_discardedLocusClosureCompl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_discardedUnion_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformIdeal_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_tower_map_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_isBlowupAlongIdealSheaf_blowupMorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_nontrivialIndex_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_center
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_length
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_withoutIsoBlowups_schemeAt
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complOpensOfIsClosed
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isBlowupAlongIdealSheaf_of_isIso_comp
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_eq_ker_of_isIso_comp
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_P2M_FunctorialResolution_Blowup_comap_ker_subscheme__comp_0b937eab6fcc
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_AffineSpacePrincipalizationData_strictTransformMap_comp_strictTransform__d73a75e45c4a
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_comap_ker_subscheme__comp_6d441ab4fd0b
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_comap___eq_ker_morphismRestrict_3254f25617a8
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_strictTransform_congr_of_comap___eq_ef196e5dd686
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.blowupSequence_tower
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.discardedUnion_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.strictTransformIdeal_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.nontrivialIndex_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_center
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_length
attribute [local simp] FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.withoutIsoBlowups_schemeAt
attribute [local simp] FunctorialResolution.EmbeddedResolution.coe_complOpensOfIsClosed
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem noetherianSpace_of_isClosedImmersion {A B : Scheme.{u}} (f : A ⟶ B)
    [AlgebraicGeometry.IsClosedImmersion f]
    (h : TopologicalSpace.NoetherianSpace ↥B) : TopologicalSpace.NoetherianSpace ↥A := by
  have := h
  exact (Scheme.Hom.isClosedEmbedding f).toIsEmbedding.toIsInducing.noetherianSpace
private theorem noetherianSpace_of_isOpenImmersion {A B : Scheme.{u}} (f : A ⟶ B)
    [AlgebraicGeometry.IsOpenImmersion f]
    (h : TopologicalSpace.NoetherianSpace ↥B) : TopologicalSpace.NoetherianSpace ↥A := by
  have := h
  exact f.isOpenEmbedding.toIsEmbedding.toIsInducing.noetherianSpace
private theorem range_comp_base {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range ⇑(f ≫ g).base = ⇑g.base '' Set.range ⇑f.base := by
  ext x
  simp [Set.range_comp]
private theorem ker_eq_ker_of_iso_hom_comp {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T)
    (e : A ≅ B) (h : e.hom ≫ g = f) : Scheme.Hom.ker f = Scheme.Hom.ker g := by
  have : CategoryTheory.IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  exact ker_eq_ker_of_isIso_comp f g e.hom h
private theorem ker_comp_comap_ι_eq_of_preimage_subset {A X : Scheme.{u}} (a : A ⟶ X)
    (U : X.Opens) (V : A.Opens)
    (hle : ((a ⁻¹ᵁ U : A.Opens) : Set ↥A) ⊆ ((V : A.Opens) : Set ↥A))
    [AlgebraicGeometry.QuasiCompact a]
    [AlgebraicGeometry.QuasiCompact (Scheme.Opens.ι V ≫ a)] :
    (Scheme.Hom.ker (Scheme.Opens.ι V ≫ a)).comap (Scheme.Opens.ι U)
      = (Scheme.Hom.ker a).comap (Scheme.Opens.ι U) := by
  have hcoePre : ((Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U) : (V.toScheme).Opens) :
        Set ↥(V.toScheme))
      = ⇑(Scheme.Opens.ι V).base ⁻¹' ((a ⁻¹ᵁ U : A.Opens) : Set ↥A) := rfl
  have hrangeV : Set.range ⇑(Scheme.Opens.ι V).base = ((V : A.Opens) : Set ↥A) :=
    Scheme.Opens.range_ι V
  have hrange : Set.range
        ⇑(Scheme.Opens.ι (Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U)) ≫ Scheme.Opens.ι V).base
      = Set.range ⇑(Scheme.Opens.ι (a ⁻¹ᵁ U)).base := by
    rw [range_comp_base, Scheme.Opens.range_ι, Scheme.Opens.range_ι, hcoePre,
      Set.image_preimage_eq_inter_range, hrangeV, Set.inter_eq_self_of_subset_left hle]
  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
      (Scheme.Opens.ι (Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U)) ≫ Scheme.Opens.ι V)
      (Scheme.Opens.ι (a ⁻¹ᵁ U)) hrange
  have h1 : ((Scheme.Opens.ι V ≫ a) ∣_ U) ≫ Scheme.Opens.ι U
      = Scheme.Opens.ι (Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U)) ≫ (Scheme.Opens.ι V ≫ a) :=
    morphismRestrict_ι (Scheme.Opens.ι V ≫ a) U
  have hcomm : (IsOpenImmersion.isoOfRangeEq
        (Scheme.Opens.ι (Scheme.Opens.ι V ⁻¹ᵁ (a ⁻¹ᵁ U)) ≫ Scheme.Opens.ι V)
        (Scheme.Opens.ι (a ⁻¹ᵁ U)) hrange).hom ≫ (a ∣_ U)
      = (Scheme.Opens.ι V ≫ a) ∣_ U := by
    refine (cancel_mono (Scheme.Opens.ι U)).mp ?_
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hfac]
    exact (Category.assoc _ _ _).trans h1.symm
  rw [ker_comap_ι_eq_ker_morphismRestrict (Scheme.Opens.ι V ≫ a) U,
    ker_comap_ι_eq_ker_morphismRestrict a U]
  exact ker_eq_ker_of_iso_hom_comp _ _ _ hcomm
private theorem image_mem_irreducibleComponents_of_isOpenEmbedding {A B : Type u} [TopologicalSpace A]
    [TopologicalSpace B] (f : A → B) (hf : Topology.IsOpenEmbedding f)
    (hcl : IsClosed (Set.range f)) {T : Set A} (hT : T ∈ irreducibleComponents A) :
    f '' T ∈ irreducibleComponents B := by
  have hTirr : IsIrreducible T := hT.1
  have hmax : ∀ ⦃D : Set B⦄, IsIrreducible D → f '' T ≤ D → D ≤ f '' T := by
    intro D hD hsubD
    have hDr : D ⊆ Set.range f := by
      by_contra hcon
      obtain ⟨z, hzD, hz⟩ := Set.not_subset.mp hcon
      obtain ⟨a0, ha0⟩ := hTirr.1
      have hw : (D ∩ Set.range f).Nonempty := ⟨f a0, hsubD ⟨a0, ha0, rfl⟩, ⟨a0, rfl⟩⟩
      obtain ⟨y, -, hy1, hy2⟩ :=
        hD.2 (Set.range f) (Set.range f)ᶜ hf.isOpen_range hcl.isOpen_compl hw ⟨z, hzD, hz⟩
      exact hy2 hy1
    have hpre : IsIrreducible (f ⁻¹' D) := by
      constructor
      · obtain ⟨b, hb⟩ := hD.1
        obtain ⟨a, rfl⟩ := hDr hb
        exact ⟨a, hb⟩
      · intro O₁ O₂ hO₁ hO₂ h₁ h₂
        obtain ⟨x₁, hx₁D, hx₁O⟩ := h₁
        obtain ⟨x₂, hx₂D, hx₂O⟩ := h₂
        obtain ⟨y, hyD, hy1, hy2⟩ :=
          hD.2 (f '' O₁) (f '' O₂) (hf.isOpenMap _ hO₁) (hf.isOpenMap _ hO₂)
            ⟨f x₁, hx₁D, ⟨x₁, hx₁O, rfl⟩⟩ ⟨f x₂, hx₂D, ⟨x₂, hx₂O, rfl⟩⟩
        obtain ⟨a₁, ha₁, ha₁e⟩ := hy1
        obtain ⟨a₂, ha₂, ha₂e⟩ := hy2
        refine ⟨a₂, ?_, ?_, ha₂⟩
        · show f a₂ ∈ D
          rw [ha₂e]
          exact hyD
        · have hEq : a₂ = a₁ := hf.injective (ha₂e.trans ha₁e.symm)
          rw [hEq]
          exact ha₁
    have hTle : T ≤ f ⁻¹' D := fun x hx => hsubD ⟨x, hx, rfl⟩
    intro y hy
    obtain ⟨a, rfl⟩ := hDr hy
    exact ⟨a, hT.2 hpre hTle hy, rfl⟩
  exact ⟨hTirr.image f hf.continuous.continuousOn, hmax⟩
namespace AffineSpacePrincipalizationData
variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  (S : AffineSpacePrincipalizationData k Y pY)
private theorem isBlowupAlongIdealSheaf_coprodDesc_of_restrict (i : ℕ)
    [AlgebraicGeometry.IsReduced (S.strictTransform i)]
    (hN : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (hopen : IsOpen (S.discardedLocus i))
    (hf : Set.range ⇑(S.strictTransformMap i).base ⊆ Set.range ⇑(S.discardedLocusClosureCompl i).ι.base)
    (hkey : Blowup.IsBlowupAlongIdealSheaf (IsOpenImmersion.lift (S.discardedLocusClosureCompl i).ι (S.strictTransformMap i) hf)
      ((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι)) :
    Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.discardedι i)) (S.centerOffDetached i) := by
  have := hN
  have hUcoe : ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = (S.discardedLocus i)ᶜ := by
    rw [S.coe_discardedLocusClosureCompl i, S.coe_discardedLocusClosure i]
  have hVcoe : ((S.discardedLocusOpens i hopen : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = S.discardedLocus i := rfl
  have hcompl : IsCompl (S.discardedLocusClosureCompl i) (S.discardedLocusOpens i hopen) := by
    constructor
    · rw [disjoint_iff]
      refine TopologicalSpace.Opens.ext ?_
      rw [TopologicalSpace.Opens.coe_inf, hUcoe, hVcoe, TopologicalSpace.Opens.coe_bot]
      exact Set.compl_inter_self _
    · rw [codisjoint_iff]
      refine TopologicalSpace.Opens.ext ?_
      rw [TopologicalSpace.Opens.coe_sup, hUcoe, hVcoe, TopologicalSpace.Opens.coe_top]
      exact Set.compl_union_self _
  obtain ⟨e', he'⟩ := S.exists_iso_discardedSubscheme_discardedLocusOpens i hN hopen
  have hg : Set.range ⇑(S.discardedι i).base ⊆ Set.range ⇑(S.discardedLocusOpens i hopen).ι.base := by
    rw [← he']
    rintro _ ⟨z, rfl⟩
    exact ⟨⇑e'.hom.base z, by simp⟩
  have hliftV : IsOpenImmersion.lift (S.discardedLocusOpens i hopen).ι (S.discardedι i) hg = e'.hom := by
    refine (cancel_mono (S.discardedLocusOpens i hopen).ι).mp ?_
    rw [IsOpenImmersion.lift_fac, he']
  have : CategoryTheory.IsIso
      (IsOpenImmersion.lift (S.discardedLocusOpens i hopen).ι (S.discardedι i) hg) := by
    rw [hliftV]
    infer_instance
  have hNU : TopologicalSpace.NoetherianSpace ↥((S.discardedLocusClosureCompl i).toScheme) :=
    noetherianSpace_of_isOpenImmersion (S.discardedLocusClosureCompl i).ι hN
  have hNsub : TopologicalSpace.NoetherianSpace
      ↥(((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subscheme) :=
    noetherianSpace_of_isClosedImmersion
      ((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι hNU
  have hq1 : AlgebraicGeometry.QuasiCompact
      ((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι := inferInstance
  have hq2 : AlgebraicGeometry.QuasiCompact
      (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
        (S.discardedLocusClosureCompl i).ι) := inferInstance
  have hJU : (S.centerOffDetached i).comap (S.discardedLocusClosureCompl i).ι
      = (S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι := by
    rw [S.centerOffDetached_eq i]
    exact comap_ker_subschemeι_comp _ _
  have hJV : (S.centerOffDetached i).comap (S.discardedLocusOpens i hopen).ι = ⊤ := by
    rw [S.centerOffDetached_eq i]
    refine Blowup.comap_eq_top_of_notMem_support _ _ ?_
    intro x hx
    have hx' : ⇑(S.discardedLocusOpens i hopen).ι.base x ∈
        ((Scheme.Hom.ker (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
          (S.discardedLocusClosureCompl i).ι)).support : Set ↥(S.strictTransform i)) := hx
    rw [Scheme.Hom.support_ker (((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
      (S.discardedLocusClosureCompl i).ι)] at hx'
    have hsubU : Set.range ⇑((((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι ≫
        (S.discardedLocusClosureCompl i).ι)).base
        ⊆ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [← Scheme.Opens.range_ι (S.discardedLocusClosureCompl i)]
      rintro _ ⟨z, rfl⟩
      exact ⟨⇑(((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι).subschemeι).base z, by simp⟩
    have hclosedU : IsClosed
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [hUcoe]
      exact hopen.isClosed_compl
    have hmem := closure_minimal hsubU hclosedU hx'
    rw [hUcoe] at hmem
    refine hmem ?_
    have h0 : ⇑(S.discardedLocusOpens i hopen).ι.base x ∈
        Set.range ⇑(S.discardedLocusOpens i hopen).ι.base := Set.mem_range_self x
    rw [Scheme.Opens.range_ι] at h0
    exact h0
  have hoi : ∀ b : Bool, AlgebraicGeometry.IsOpenImmersion
      (Bool.rec (motive := fun b : Bool =>
          (cond b (S.discardedLocusClosureCompl i).toScheme (S.discardedLocusOpens i hopen).toScheme) ⟶ S.strictTransform i)
        (S.discardedLocusOpens i hopen).ι (S.discardedLocusClosureCompl i).ι b) := by
    intro b
    cases b
    · exact inferInstanceAs
        (AlgebraicGeometry.IsOpenImmersion (S.discardedLocusOpens i hopen).ι)
    · exact inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (S.discardedLocusClosureCompl i).ι)
  refine Blowup.IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover _ _
    (fun b : Bool => cond b (S.discardedLocusClosureCompl i).toScheme (S.discardedLocusOpens i hopen).toScheme)
    (Bool.rec (motive := fun b : Bool =>
        (cond b (S.discardedLocusClosureCompl i).toScheme (S.discardedLocusOpens i hopen).toScheme) ⟶ S.strictTransform i)
      (S.discardedLocusOpens i hopen).ι (S.discardedLocusClosureCompl i).ι) ?_ ?_
  · intro x
    by_cases hx : x ∈ S.discardedLocus i
    · refine ⟨false, ?_⟩
      show x ∈ Set.range ⇑(S.discardedLocusOpens i hopen).ι.base
      rw [Scheme.Opens.range_ι]
      exact hx
    · refine ⟨true, ?_⟩
      show x ∈ Set.range ⇑(S.discardedLocusClosureCompl i).ι.base
      rw [Scheme.Opens.range_ι, hUcoe]
      exact hx
  · intro b
    cases b
    · show Blowup.IsBlowupAlongIdealSheaf (pullback.snd (coprod.desc (S.strictTransformMap i) (S.discardedι i))
        (S.discardedLocusOpens i hopen).ι) ((S.centerOffDetached i).comap (S.discardedLocusOpens i hopen).ι)
      rw [hJV]
      obtain ⟨e, he1, _⟩ :=
        Blowup.exists_iso_pullback_coprod_desc_right (S.strictTransformMap i) (S.discardedι i) hcompl hf hg
      have : CategoryTheory.IsIso (pullback.snd (coprod.desc (S.strictTransformMap i) (S.discardedι i))
          (S.discardedLocusOpens i hopen).ι) := by
        rw [← he1]
        infer_instance
      exact Blowup.IsBlowupAlongIdealSheaf.of_isIso _
    · show Blowup.IsBlowupAlongIdealSheaf (pullback.snd (coprod.desc (S.strictTransformMap i) (S.discardedι i))
        (S.discardedLocusClosureCompl i).ι) ((S.centerOffDetached i).comap (S.discardedLocusClosureCompl i).ι)
      rw [hJU]
      obtain ⟨e, he1, _⟩ :=
        Blowup.exists_iso_pullback_coprod_desc_left (S.strictTransformMap i) (S.discardedι i) hcompl hf hg
      exact isBlowupAlongIdealSheaf_of_isIso_comp _ _ e.hom he1 _ hkey
private theorem isBlowupAlongIdealSheaf_lift_discardedLocusClosureCompl (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (i : ℕ)
    (hi : i < S.ambientLength) (hNlev : AlgebraicGeometry.IsNoetherian (S.ambientLevel i))
    (hNoetherian : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (hopen : IsOpen (S.discardedLocus i))
    (hf : Set.range ⇑(S.strictTransformMap i).base ⊆ Set.range ⇑(S.discardedLocusClosureCompl i).ι.base) :
    Blowup.IsBlowupAlongIdealSheaf (IsOpenImmersion.lift (S.discardedLocusClosureCompl i).ι (S.strictTransformMap i) hf)
      ((S.comapAmbientCenter i).comap (S.discardedLocusClosureCompl i).ι) := by
  have := hNlev
  have := hNoetherian
  have hUcoe : ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = (S.discardedLocus i)ᶜ := by
    rw [S.coe_discardedLocusClosureCompl i, S.coe_discardedLocusClosure i]
  have hUclosed : IsClosed ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) :
      Set ↥(S.strictTransform i)) := by
    rw [hUcoe]
    exact hopen.isClosed_compl
  have hrangeU : Set.range ⇑(S.discardedLocusClosureCompl i).ι.base
      = ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) :=
    Scheme.Opens.range_ι _
  have hclos : AlgebraicGeometry.IsClosedImmersion ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i) := by
    refine AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _ ?_
    have hcl2 : IsClosed (⇑(S.strictTransformι i).base ''
        ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) :=
      (Scheme.Hom.isClosedEmbedding (S.strictTransformι i)).isClosedMap _ hUclosed
    have hr : Set.range ⇑((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i).base
        = ⇑(S.strictTransformι i).base ''
          ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [range_comp_base, hrangeU]
    have hfin : IsClosed (Set.range ⇑((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i).base) := by
      rw [hr]
      exact hcl2
    exact hfin
  have hIcomp : ∀ T ∈ irreducibleComponents ↥((S.discardedLocusClosureCompl i).toScheme),
      ¬ (⇑((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i).base '' T
        ⊆ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i))) := by
    intro T hT hsub
    have hCmem : ⇑(S.discardedLocusClosureCompl i).ι.base '' T
        ∈ irreducibleComponents ↥(S.strictTransform i) := by
      refine image_mem_irreducibleComponents_of_isOpenEmbedding _ (S.discardedLocusClosureCompl i).ι.isOpenEmbedding ?_ hT
      rw [hrangeU]
      exact hUclosed
    have himg : ⇑((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i).base '' T
        = ⇑(S.strictTransformι i).base '' (⇑(S.discardedLocusClosureCompl i).ι.base '' T) := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨_, ⟨t, ht, rfl⟩, by simp⟩
      · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨t, ht, by simp⟩
    rw [himg] at hsub
    have hDiscarded : ⇑(S.discardedLocusClosureCompl i).ι.base '' T ∈ S.discardedComponents i := ⟨hCmem, hsub⟩
    obtain ⟨t, ht⟩ := hT.1.1
    have h1 : ⇑(S.discardedLocusClosureCompl i).ι.base t ∈ S.discardedLocus i :=
      Set.subset_sUnion_of_mem hDiscarded ⟨t, ht, rfl⟩
    have h2 : ⇑(S.discardedLocusClosureCompl i).ι.base t
        ∈ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [← hrangeU]
      exact Set.mem_range_self t
    rw [hUcoe] at h2
    exact h2 h1
  have hqι : AlgebraicGeometry.QuasiCompact (S.strictTransformι i) := inferInstance
  have hqj : AlgebraicGeometry.QuasiCompact ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i) := inferInstance
  have hOU : ((S.strictTransformι i ⁻¹ᵁ (S.ambientCenter i).support.compl :
        (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      ⊆ ((S.discardedLocusClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    intro x hx
    have hx' : ⇑(S.strictTransformι i).base x
        ∉ ((S.ambientCenter i).support : Set ↥(S.ambientLevel i)) := hx
    rw [hUcoe]
    intro hDisc
    exact hx' (S.image_discardedLocus_subset_support i ⟨x, hDisc, rfl⟩)
  have hkerRestr := ker_comp_comap_ι_eq_of_preimage_subset (S.strictTransformι i) (S.ambientCenter i).support.compl
    (S.discardedLocusClosureCompl i) hOU
  have hKerStrict : Scheme.Hom.ker (S.strictTransformι i) = S.strictTransformIdeal i :=
    Scheme.IdealSheafData.ker_subschemeι (S.strictTransformIdeal i)
  have hST : Blowup.strictTransform (S.ambientBlowupMorphism i) (S.ambientCenter i)
      (Scheme.Hom.ker ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i)) = S.strictTransformIdeal (i + 1) := by
    rw [S.strictTransformIdeal_succ i]
    refine strictTransform_congr_of_comap_ι_eq (S.ambientBlowupMorphism i) (S.ambientCenter i) _ _ ?_
    rw [hkerRestr, hKerStrict]
  have hstat := hres (S.ambientLevel i) (S.ambientLevel (i + 1)) ((S.discardedLocusClosureCompl i).toScheme)
      ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i) (S.ambientBlowupMorphism i) (S.ambientCenter i)
      (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) hIcomp
  rw [hST] at hstat
  obtain ⟨ψ, hψfac, hψbl⟩ := hstat
  have : Mono ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i) := inferInstance
  have hψ : ψ = IsOpenImmersion.lift (S.discardedLocusClosureCompl i).ι (S.strictTransformMap i) hf := by
    refine (cancel_mono ((S.discardedLocusClosureCompl i).ι ≫ S.strictTransformι i)).mp ?_
    rw [hψfac, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact (S.strictTransformMap_comp_strictTransformι i).symm
  rw [hψ] at hψbl
  rw [Scheme.IdealSheafData.comap_comp] at hψbl
  exact hψbl
end AffineSpacePrincipalizationData
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hiso : EmbeddedPrincipalizationDiscardedLocusIsOpen A hemb hsnc hsm)
    (hnoeth : EmbeddedPrincipalizationAmbientIsNoetherian A hemb hsnc hsm)
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  set S := AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY with hSdef
  intro i hi
  have hopen : IsOpen (S.discardedLocus i) := hiso k Y pY i hi
  have hNlev : ∀ j, j ≤ S.ambientLength → TopologicalSpace.NoetherianSpace ↥(S.ambientLevel j) := by
    intro j hj
    have : AlgebraicGeometry.IsNoetherian (S.ambientLevel j) := hnoeth k Y pY j hj
    infer_instance
  have hNoetherian : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform_of_ambientLevel i (hNlev i (le_of_lt hi))
  have hRed : AlgebraicGeometry.IsReduced (S.strictTransform i) :=
    S.isReduced_strictTransform (fun j hj => hnoeth k Y pY j hj) i (le_of_lt hi)
  have hf : Set.range ⇑(S.strictTransformMap i).base ⊆ Set.range ⇑(S.discardedLocusClosureCompl i).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact S.range_strictTransformMap_subset_discardedLocusClosureCompl i hi hNoetherian (hNlev (i + 1) hi) hopen
  have hkey := S.isBlowupAlongIdealSheaf_lift_discardedLocusClosureCompl hres i hi (hnoeth k Y pY i (le_of_lt hi))
    hNoetherian hopen hf
  rw [S.tower_map_succ i]
  exact S.isBlowupAlongIdealSheaf_transitionMap_of_coprodDesc i
    (AffineSpacePrincipalizationData.isBlowupAlongIdealSheaf_coprodDesc_of_restrict S i hNoetherian hopen hf hkey)
end FunctorialResolution.EmbeddedResolution
