-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.affineEmbedsIntoAffineSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:21:58.321165+00:00
-- url     : https://prove2.me/submissions/542cf48f-7975-4524-a9de-ba2fd9825b9e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineEmbeddingIntoAffineSpace
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem extension_X_last_eq_zero {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) :
    extendAlgHomLastVarZero f (MvPolynomial.X (ULift.up (Fin.last n))) = 0 := by
  simp [extendAlgHomLastVarZero]
private theorem extension_surjective {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f) :
    Function.Surjective (extendAlgHomLastVarZero f) := by
  intro a
  obtain ⟨q, rfl⟩ := hf a
  refine ⟨MvPolynomial.rename
    (fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1)))) q, ?_⟩
  show MvPolynomial.aeval (fun i : ULift.{u} (Fin (n + 1)) =>
      Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down)
      (MvPolynomial.rename (fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1)))) q)
      = f q
  rw [MvPolynomial.aeval_rename]
  have h : ((fun i : ULift.{u} (Fin (n + 1)) =>
      Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down) ∘
      fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1))))
      = fun j : Fin n => f (MvPolynomial.X j) := by
    funext j
    simp
  rw [h]
  exact DFunLike.congr_fun (MvPolynomial.aeval_unique f).symm q
private theorem isoSpec_hom_comp_spec_map_appTop {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) :
    Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop) = p := by
  have h2 : Y.isoSpec.hom = Y.toSpecΓ := rfl
  rw [h2, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality p,
    ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]
private theorem isClosedImmersion_embedding_and_comp_eq {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (p : Y ⟶ Spec (CommRingCat.of k))
    (halg : algebraMap k ↥Γ(Y, ⊤)
      = (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom))
    (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤)) (hg : Function.Surjective g) :
    IsClosedImmersion (toAffineSpaceOfAlgHom Y g) ∧
      toAffineSpaceOfAlgHom Y g ≫ (affineSpaceIndexedBy k m ↘ Spec (CommRingCat.of k)) = p := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  constructor
  · show IsClosedImmersion (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv)
    infer_instance
  · show (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv) ≫
      (affineSpaceIndexedBy k m ↘ Spec (CommRingCat.of k)) = p
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    have h2 : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial m k) ≫
        CommRingCat.ofHom g.toRingHom
        = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop := by
      refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
      show g (MvPolynomial.C a) = _
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, halg]
    rw [h2]
    exact isoSpec_hom_comp_spec_map_appTop Y p
private theorem isIrreducible_univ_affineSpaceIndexedBy (k : Type u) [Field k] (m : Type u) :
    IsIrreducible (Set.univ : Set ↥(affineSpaceIndexedBy k m)) := by
  have h0 : IsIrreducible (Set.univ : Set ↥(Spec (CommRingCat.of (MvPolynomial m k)))) :=
    IrreducibleSpace.isIrreducible_univ (PrimeSpectrum (MvPolynomial m k))
  have h1 := h0.image (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm)
    (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm).continuous.continuousOn
  rwa [Set.image_univ,
    (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm).surjective.range_eq] at h1
private theorem eq_univ_of_mem_irreducibleComponents_of_isIrreducible_univ {X : Type u} [TopologicalSpace X]
    (h : IsIrreducible (Set.univ : Set X)) {T : Set X} (hT : T ∈ irreducibleComponents X) :
    T = Set.univ :=
  Set.eq_univ_of_univ_subset (hT.2 h (Set.subset_univ T))
private theorem support_ker_ne_univ_of_map_X_eq_zero {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤))
    (x₀ : m) (hx₀ : g (MvPolynomial.X x₀) = 0) [QuasiCompact (toAffineSpaceOfAlgHom Y g)] :
    ((toAffineSpaceOfAlgHom Y g).ker.support : Set ↥(affineSpaceIndexedBy k m)) ≠ Set.univ := by
  intro hcon
  have hcomp : toAffineSpaceOfAlgHom Y g ≫ (AffineSpace.SpecIso m (CommRingCat.of k)).hom
      = Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
    show (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).hom = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmem0 : ∀ w : PrimeSpectrum ↥Γ(Y, ⊤),
      (MvPolynomial.X x₀ : MvPolynomial m k) ∈
        ((Spec.map (CommRingCat.ofHom g.toRingHom)).base w).asIdeal := by
    intro w
    show g (MvPolynomial.X x₀) ∈ w.asIdeal
    rw [hx₀]
    exact Ideal.zero_mem _
  obtain ⟨v, hv, hvcont, hvsurj⟩ :
      ∃ v : ↥(affineSpaceIndexedBy k m) → PrimeSpectrum (MvPolynomial m k),
        (∀ y : ↥Y, v ((toAffineSpaceOfAlgHom Y g).base y)
            = (Spec.map (CommRingCat.ofHom g.toRingHom)).base (Y.isoSpec.hom.base y)) ∧
          Continuous v ∧ Function.Surjective v := by
    refine ⟨fun x => (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))) x, ?_, ?_, ?_⟩
    · intro y
      exact congrArg
        (fun φ : Y ⟶ Spec (CommRingCat.of (MvPolynomial m k)) => φ.base y) hcomp
    · exact (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))).continuous
    · exact (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))).surjective
  have hrange : ∀ y : ↥Y,
      (MvPolynomial.X x₀ : MvPolynomial m k) ∈ (v ((toAffineSpaceOfAlgHom Y g).base y)).asIdeal := by
    intro y
    rw [hv y]
    exact hmem0 _
  have hsub : Set.range (toAffineSpaceOfAlgHom Y g).base ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
    rintro _ ⟨y, rfl⟩
    have : v ((toAffineSpaceOfAlgHom Y g).base y) ∈
        PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact hrange y
    exact this
  have hsupp : ((toAffineSpaceOfAlgHom Y g).ker.support : Set ↥(affineSpaceIndexedBy k m))
      = closure (Set.range (toAffineSpaceOfAlgHom Y g).base) := Scheme.Hom.support_ker _
  have huniv : (Set.univ : Set ↥(affineSpaceIndexedBy k m)) ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
    rw [← hcon, hsupp]
    exact closure_minimal hsub ((PrimeSpectrum.isClosed_zeroLocus _).preimage hvcont)
  obtain ⟨ξ, hξ⟩ := hvsurj ⟨⊥, Ideal.isPrime_bot⟩
  have hmem : ξ ∈ v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} :=
    huniv (Set.mem_univ ξ)
  rw [Set.mem_preimage, hξ, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hmem
  have h6 : (MvPolynomial.X x₀ : MvPolynomial m k) = 0 := Ideal.mem_bot.mp hmem
  have h7 : (1 : k) = 0 := by
    have h8 := congrArg (MvPolynomial.coeff (Finsupp.single x₀ 1)) h6
    simp at h8
  exact one_ne_zero h7
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution : AffineEmbedsIntoAffineSpace.{u} := by
  intro k _ Y _ p _
  have hft : RingHom.FiniteType (p.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := p)).mp inferInstance
  have hiso : Function.Surjective ⇑((Scheme.ΓSpecIso (CommRingCat.of k)).inv) := by
    intro x
    exact ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom x, by simp⟩
  have hφ : RingHom.FiniteType
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom) := by
    rw [CommRingCat.hom_comp]
    exact hft.comp (RingHom.FiniteType.of_surjective _ hiso)
  let _ : Algebra k ↥Γ(Y, ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom).toAlgebra
  have halg : algebraMap k ↥Γ(Y, ⊤)
      = (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom) := rfl
  have hfta : Algebra.FiniteType k ↥Γ(Y, ⊤) := hφ
  obtain ⟨n, f, hfsurj⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hfta
  obtain ⟨hci, hover⟩ := isClosedImmersion_embedding_and_comp_eq Y p halg (extendAlgHomLastVarZero f) (extension_surjective f hfsurj)
  have := hci
  refine ⟨n + 1, toAffineSpaceOfAlgHom Y (extendAlgHomLastVarZero f), hci, ?_, hover⟩
  have hne := support_ker_ne_univ_of_map_X_eq_zero Y (extendAlgHomLastVarZero f) (ULift.up (Fin.last n)) (extension_X_last_eq_zero f)
  have hirr := isIrreducible_univ_affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1)))
  have key : ∀ T ∈ irreducibleComponents ↥(affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1)))),
      ¬ T ⊆ ((toAffineSpaceOfAlgHom Y (extendAlgHomLastVarZero f)).ker.support :
        Set ↥(affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1))))) := by
    intro T hT hsubT
    refine hne (Set.eq_univ_of_univ_subset ?_)
    rw [← eq_univ_of_mem_irreducibleComponents_of_isIrreducible_univ hirr hT]
    exact hsubT
  exact key
end FunctorialResolution.EmbeddedResolution
