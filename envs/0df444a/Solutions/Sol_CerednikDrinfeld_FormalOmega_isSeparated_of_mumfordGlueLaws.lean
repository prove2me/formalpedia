-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.isSeparated_of_mumfordGlueLaws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/485f399f-f8c9-59a0-ad0b-56a822adbf0f

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover
import Theorems.Thm_CerednikDrinfeld_FormalOmega_range_sup_range_comp_eq_top_of_isPullback_chartVRing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_associated_algEquiv_chartERing_xi_eta_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_isSeparated_of_mumfordGlueLaws
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
set_option linter.unusedSimpArgs false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega~stalk"

universe u

namespace LevelSep

section Generic

theorem isClosedImmersion_of_preimage_pair {X Y : Scheme.{u}} (f : X ⟶ Y) (V₀ V₁ : Y.Opens)
    (hV : Disjoint V₀ V₁) (hcov : f ⁻¹ᵁ V₀ ⊔ f ⁻¹ᵁ V₁ = ⊤)
    (h₀ : IsClosedImmersion ((f ⁻¹ᵁ V₀).ι ≫ f)) (h₁ : IsClosedImmersion ((f ⁻¹ᵁ V₁).ι ≫ f)) :
    IsClosedImmersion f := by

  let U : Bool → X.Opens := fun b => if b then f ⁻¹ᵁ V₁ else f ⁻¹ᵁ V₀
  have hU : IsOpenCover U := by
    refine IsOpenCover.mk ?_
    rw [iSup_bool_eq]
    show f ⁻¹ᵁ V₁ ⊔ f ⁻¹ᵁ V₀ = ⊤
    rw [sup_comm, hcov]
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover U hU

  haveI hst : SurjectiveOnStalks f := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SurjectiveOnStalks) 𝒰]
    intro b
    cases b
    · show SurjectiveOnStalks ((f ⁻¹ᵁ V₀).ι ≫ f); infer_instance
    · show SurjectiveOnStalks ((f ⁻¹ᵁ V₁).ι ≫ f); infer_instance

  have hmem : ∀ x : X, f.base x ∈ (V₀ : Set Y) ∨ f.base x ∈ (V₁ : Set Y) := by
    intro x
    have hx : x ∈ (f ⁻¹ᵁ V₀ ⊔ f ⁻¹ᵁ V₁ : X.Opens) := by rw [hcov]; trivial
    exact hx
  have hdis : Disjoint (V₀ : Set Y) V₁ := TopologicalSpace.Opens.coe_disjoint.mpr hV

  have hres : ∀ (W : Y.Opens) (x : X) (hx : f.base x ∈ (W : Set Y)),
      ((f ⁻¹ᵁ W).ι ≫ f).base (⟨x, hx⟩ : ↥(f ⁻¹ᵁ W)) = f.base x := fun W x hx => rfl

  have hinj : ∀ (W : Y.Opens), IsClosedImmersion ((f ⁻¹ᵁ W).ι ≫ f) →
      ∀ (a b : X) (ha : f.base a ∈ (W : Set Y)) (hb : f.base b ∈ (W : Set Y)), f.base a = f.base b → a = b := by
    intro W hW a b ha hb hab
    have h := ((f ⁻¹ᵁ W).ι ≫ f).isClosedEmbedding.injective
      (a₁ := (⟨a, ha⟩ : ↥(f ⁻¹ᵁ W))) (a₂ := (⟨b, hb⟩ : ↥(f ⁻¹ᵁ W))) (by rw [hres, hres]; exact hab)
    exact congrArg Subtype.val h

  have hclosed : ∀ (W : Y.Opens), IsClosedImmersion ((f ⁻¹ᵁ W).ι ≫ f) → ∀ C : Set X, IsClosed C →
      IsClosed (f.base '' (C ∩ f.base ⁻¹' (W : Set Y))) := by
    intro W hW C hC
    have h := ((f ⁻¹ᵁ W).ι ≫ f).isClosedEmbedding.isClosedMap _ (hC.preimage (f ⁻¹ᵁ W).ι.continuous)
    convert h using 1
    ext y
    constructor
    · rintro ⟨x, ⟨hxC, hxW⟩, rfl⟩
      exact ⟨⟨x, hxW⟩, hxC, hres W x hxW⟩
    · rintro ⟨⟨x, hxW⟩, hxC, rfl⟩
      exact ⟨x, ⟨hxC, hxW⟩, (hres W x hxW).symm⟩
  refine { isClosedEmbedding := ?_ }
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap f.continuous ?_ ?_
  · intro a b hab
    rcases hmem a with ha | ha <;> rcases hmem b with hb | hb
    · exact hinj V₀ h₀ a b ha hb hab
    · exact absurd hb (Set.disjoint_left.mp hdis (hab ▸ ha))
    · exact absurd ha (Set.disjoint_left.mp hdis (hab.symm ▸ hb))
    · exact hinj V₁ h₁ a b ha hb hab
  · intro C hC
    have e : f.base '' C = f.base '' (C ∩ f.base ⁻¹' (V₀ : Set Y)) ∪ f.base '' (C ∩ f.base ⁻¹' (V₁ : Set Y)) := by
      rw [← Set.image_union, ← Set.inter_union_distrib_left]
      congr 1
      refine (Set.inter_eq_left.mpr ?_).symm
      intro x _
      exact hmem x
    rw [e]
    exact (hclosed V₀ h₀ C hC).union (hclosed V₁ h₁ C hC)

theorem isClosedImmersion_ι_comp_mapDesc {U U' Z S Y : Scheme.{u}} (f : U ⟶ Z) (f' : U' ⟶ Z) (q : Z ⟶ S)
    [IsOpenImmersion f] (j : Y ⟶ U') [IsOpenImmersion j] (k : Y ⟶ U) (hjk : j ≫ f' = k ≫ f)
    (W : U'.Opens) (hW : Scheme.Hom.opensRange j = W)
    (hc : IsClosedImmersion
      (pullback.lift k j (show k ≫ f ≫ q = j ≫ f' ≫ q by rw [← Category.assoc, ← hjk, Category.assoc]) :
        Y ⟶ pullback (f ≫ q) (f' ≫ q))) :
    IsClosedImmersion (((pullback.snd f f') ⁻¹ᵁ W).ι ≫ pullback.mapDesc f f' q) := by
  subst hW

  let m : Y ⟶ pullback f f' := pullback.lift k j hjk.symm
  have hm_snd : m ≫ pullback.snd f f' = j := pullback.lift_snd _ _ _
  haveI : IsOpenImmersion (pullback.snd f f') := inferInstance
  haveI : IsOpenImmersion (m ≫ pullback.snd f f') := by rw [hm_snd]; infer_instance
  haveI hm : IsOpenImmersion m := IsOpenImmersion.of_comp m (pullback.snd f f')

  have hrange : Set.range m.base = ((pullback.snd f f') ⁻¹ᵁ j.opensRange : Set ↥(pullback f f')) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      show (pullback.snd f f').base (m.base y) ∈ Set.range j.base
      exact ⟨y, (congrArg (fun φ : Y ⟶ U' => φ.base y) hm_snd).symm⟩
    · intro p hp
      obtain ⟨y, hy⟩ := hp
      refine ⟨y, (pullback.snd f f').isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun φ : Y ⟶ U' => φ.base y) hm_snd).trans hy
  let e : Y ≅ ↑((pullback.snd f f') ⁻¹ᵁ j.opensRange) :=
    IsOpenImmersion.isoOfRangeEq m ((pullback.snd f f') ⁻¹ᵁ j.opensRange).ι (by rw [hrange, Scheme.Opens.range_ι])
  have he : e.hom ≫ ((pullback.snd f f') ⁻¹ᵁ j.opensRange).ι = m := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

  have key : ((pullback.snd f f') ⁻¹ᵁ j.opensRange).ι ≫ pullback.mapDesc f f' q =
      e.inv ≫ pullback.lift k j (show k ≫ f ≫ q = j ≫ f' ≫ q by rw [← Category.assoc, ← hjk, Category.assoc]) := by
    rw [(Iso.eq_inv_comp e).mpr he, Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [pullback.mapDesc, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id]
      exact pullback.lift_fst _ _ _
    · simp only [pullback.mapDesc, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
      exact pullback.lift_snd _ _ _
  rw [key]
  infer_instance

theorem isClosedImmersion_lift_of_range_sup_range_eq_top
    {R A A' V : Type u} [CommRing R] [CommRing A] [CommRing A'] [CommRing V] [Algebra R A] [Algebra R A'] [Algebra R V]
    (fS : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (fS' : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of R))
    (hfS : fS = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hfS' : fS' = Spec.map (CommRingCat.ofHom (algebraMap R A')))
    (φ : A →ₐ[R] V) (ψ : A' →ₐ[R] V) (hsup : φ.range ⊔ ψ.range = ⊤)
    (w : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fS = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ fS') :
    IsClosedImmersion (pullback.lift (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom ψ.toRingHom)) w) := by
  subst hfS hfS'

  have hsurj : Function.Surjective (Algebra.TensorProduct.productMap φ ψ) := by
    rw [← AlgHom.range_eq_top, Algebra.TensorProduct.productMap_range, hsup]
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap φ ψ).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have hlift : pullback.lift (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom ψ.toRingHom)) w =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap φ ψ).toRingHom) ≫ (pullbackSpecIso R A A').inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      rw [← CommRingCat.ofHom_comp]
      congr 1
      ext a
      exact (Algebra.TensorProduct.productMap_left_apply φ ψ a).symm
    · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      rw [← CommRingCat.ofHom_comp]
      congr 1
      ext a
      exact (Algebra.TensorProduct.productMap_right_apply φ ψ a).symm
  rw [hlift]
  infer_instance

theorem isClosedImmersion_mapDesc_of_eq_comp {U U' Z S : Scheme.{u}} (f : U ⟶ Z) (f' : U' ⟶ Z) (q : Z ⟶ S)
    [Mono f] [IsSeparated (f ≫ q)] (e : U' ⟶ U) (he : f' = e ≫ f) :
    IsClosedImmersion (pullback.mapDesc f f' q) := by
  subst he
  have h1 : IsClosedImmersion (pullback.mapDesc f (e ≫ f) q ≫ pullback.snd (f ≫ q) ((e ≫ f) ≫ q)) := by
    have : pullback.mapDesc f (e ≫ f) q ≫ pullback.snd (f ≫ q) ((e ≫ f) ≫ q) = pullback.snd f (e ≫ f) := by
      simp only [pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id]
    rw [this]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd (f ≫ q) ((e ≫ f) ≫ q))

theorem isIso_spec_algEquiv {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (e : A ≃ₐ[R] A) :
    IsIso (Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom)) := by
  have : IsIso (CommRingCat.ofHom e.toAlgHom.toRingHom) :=
    ⟨⟨CommRingCat.ofHom e.symm.toAlgHom.toRingHom, by ext x; simp, by ext x; simp⟩⟩
  infer_instance

theorem disjoint_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) {V₀ V₁ : Y.Opens} (h : V₀ ⊓ V₁ = ⊥) :
    Disjoint (f ⁻¹ᵁ V₀) (f ⁻¹ᵁ V₁) := by
  rw [disjoint_iff]
  ext x
  constructor
  · rintro ⟨h0, h1⟩
    have : f x ∈ V₀ ⊓ V₁ := ⟨h0, h1⟩
    rw [h] at this
    exact this
  · intro hx
    exact hx.elim

end Generic

section Spectrum

variable {A V : Type u} [CommRing A] [CommRing V]

theorem isOpenImmersion_spec_of_away (ι : A →+* V) (x : A) (hι : @IsLocalization.Away A _ x V _ ι.toAlgebra) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ι)) := by
  letI : Algebra A V := ι.toAlgebra
  exact IsOpenImmersion.of_isLocalization (S := V) x

theorem range_spec_of_away (ι : A →+* V) (x : A) (hι : @IsLocalization.Away A _ x V _ ι.toAlgebra) :
    Set.range (Spec.map (CommRingCat.ofHom ι)) = (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) := by
  letI : Algebra A V := ι.toAlgebra
  exact PrimeSpectrum.localization_away_comap_range V x

theorem range_spec_comp_algEquiv {R : Type u} [CommRing R] [Algebra R A] [Algebra R V]
    (ι : A →ₐ[R] V) (α : A ≃ₐ[R] A) (x : A)
    (hι : Set.range (Spec.map (CommRingCat.ofHom ι.toRingHom)) = (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A))) :
    Set.range (Spec.map (CommRingCat.ofHom (ι.comp α.toAlgHom).toRingHom)) =
      (PrimeSpectrum.basicOpen (α.symm x) : Set (PrimeSpectrum A)) := by
  change Set.range (PrimeSpectrum.comap (ι.toRingHom.comp α.toAlgHom.toRingHom)) = _
  change Set.range (PrimeSpectrum.comap ι.toRingHom) = _ at hι
  ext q
  simp only [Set.mem_range, PrimeSpectrum.comap_comp_apply]
  constructor
  · rintro ⟨p, rfl⟩
    have hp : PrimeSpectrum.comap ι.toRingHom p ∈ (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) :=
      hι ▸ ⟨p, rfl⟩
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hp ⊢
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    intro h
    apply hp
    have e : α.toAlgHom.toRingHom (α.symm x) = x := α.apply_symm_apply x
    rwa [e] at h
  · intro hq
    have hq' : PrimeSpectrum.comap α.symm.toAlgHom.toRingHom q ∈
        (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) := by
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hq ⊢
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      exact hq
    rw [← hι] at hq'
    obtain ⟨p, hp⟩ := hq'
    refine ⟨p, ?_⟩
    rw [hp, ← PrimeSpectrum.comap_comp_apply]
    have : α.symm.toAlgHom.toRingHom.comp α.toAlgHom.toRingHom = RingHom.id A := by
      ext a
      exact α.symm_apply_apply a
    rw [this]
    rfl

theorem range_comp_algEquiv {R A' B C : Type*} [CommSemiring R] [Semiring A'] [Semiring B] [Semiring C]
    [Algebra R A'] [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) (e : A' ≃ₐ[R] B) :
    (f.comp (e : A' →ₐ[R] B)).range = f.range := by
  rw [AlgHom.range_comp, (AlgHom.range_eq_top (e : A' →ₐ[R] B)).2 e.surjective, Algebra.map_top]

theorem basicOpen_eq_of_associated {x y : A} (h : Associated x y) :
    PrimeSpectrum.basicOpen x = PrimeSpectrum.basicOpen y := by
  obtain ⟨u, rfl⟩ := h
  ext p
  simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
  constructor
  · intro hx hxu
    exact hx (p.2.mem_or_mem hxu |>.elim id fun hu => absurd (Ideal.eq_top_of_isUnit_mem _ hu u.isUnit) p.2.ne_top)
  · intro hxu hx
    exact hxu (Ideal.mul_mem_right _ _ hx)

theorem basicOpen_inf_eq_bot_of_isNilpotent {x y : A} (h : IsNilpotent (x * y)) :
    PrimeSpectrum.basicOpen x ⊓ PrimeSpectrum.basicOpen y = ⊥ := by
  rw [← PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_eq_bot_iff]
  exact h

end Spectrum

section Comb
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
variable (π : 𝒪) (hπ : Irreducible π)
variable (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
variable (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀)
  (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

abbrev s₀ : Vertex 𝒪 K₀ := stdVertex 𝒪 K₀

abbrev s₁ : Vertex 𝒪 K₀ := Vertex.act g₁ (stdVertex 𝒪 K₀)

abbrev Sset (g : Matrix.GeneralLinearGroup (Fin 2) K₀) : Prop :=
  (Vertex.act g (s₀ 𝒪 K₀) = s₀ 𝒪 K₀ ∧ Vertex.act g (s₁ 𝒪 K₀ g₁) = s₁ 𝒪 K₀ g₁) ∨
  (Vertex.act g (s₀ 𝒪 K₀) = s₁ 𝒪 K₀ g₁ ∧ Vertex.act g (s₁ 𝒪 K₀ g₁) = s₀ 𝒪 K₀)

abbrev SameEdge (a b : Matrix.GeneralLinearGroup (Fin 2) K₀) : Prop :=
  (Vertex.act a (s₀ 𝒪 K₀) = Vertex.act b (s₀ 𝒪 K₀) ∧ Vertex.act a (s₁ 𝒪 K₀ g₁) = Vertex.act b (s₁ 𝒪 K₀ g₁)) ∨
  (Vertex.act a (s₀ 𝒪 K₀) = Vertex.act b (s₁ 𝒪 K₀ g₁) ∧ Vertex.act a (s₁ 𝒪 K₀ g₁) = Vertex.act b (s₀ 𝒪 K₀))

theorem Sset_mul {g g' : Matrix.GeneralLinearGroup (Fin 2) K₀} (hg : Sset 𝒪 K₀ g₁ g) (hg' : Sset 𝒪 K₀ g₁ g') :
    Sset 𝒪 K₀ g₁ (g * g') := by
  unfold Sset at *
  simp only [Vertex.act_mul]
  rcases hg with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hg' with ⟨a', b'⟩ | ⟨a', b'⟩ <;>
    simp only [a', b', a, b, and_true, true_or, or_true, and_self]

theorem Sset_inv {g : Matrix.GeneralLinearGroup (Fin 2) K₀} (hg : Sset 𝒪 K₀ g₁ g) : Sset 𝒪 K₀ g₁ g⁻¹ := by
  unfold Sset at *
  have key : ∀ v w : Vertex 𝒪 K₀, Vertex.act g v = w → Vertex.act g⁻¹ w = v := by
    intro v w h; rw [← h, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]
  rcases hg with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨key _ _ a, key _ _ b⟩
  · exact Or.inr ⟨key _ _ b, key _ _ a⟩

theorem Sset_one : Sset 𝒪 K₀ g₁ 1 := Or.inl ⟨Vertex.act_one _, Vertex.act_one _⟩

theorem sameEdge_mul_of_Sset {m : Matrix.GeneralLinearGroup (Fin 2) K₀} (hm : Sset 𝒪 K₀ g₁ m)
    (b : Matrix.GeneralLinearGroup (Fin 2) K₀) : SameEdge 𝒪 K₀ g₁ (b * m) b := by
  unfold SameEdge Sset at *
  simp only [Vertex.act_mul]
  rcases hm with ⟨a, c⟩ | ⟨a, c⟩
  · exact Or.inl ⟨by rw [a], by rw [c]⟩
  · exact Or.inr ⟨by rw [a], by rw [c]⟩

def swapO : Matrix.GeneralLinearGroup (Fin 2) 𝒪 :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

def swap : Matrix.GeneralLinearGroup (Fin 2) K₀ := Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K₀) (swapO 𝒪)

theorem swap_val : ((swap 𝒪 K₀ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = !![0, 1; 1, 0] := by
  ext i j
  show algebraMap 𝒪 K₀ ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) 𝒪) i j) = _
  fin_cases i <;> fin_cases j <;> simp

theorem act_swap_s₀ : Vertex.act (swap 𝒪 K₀) (s₀ 𝒪 K₀) = s₀ 𝒪 K₀ := by
  unfold s₀
  rw [stdVertex, Vertex.act_mk]
  apply (Vertex.mk_eq_mk_iff).2
  rw [(latticeMap_stdLattice_eq_iff_mem_range (swap 𝒪 K₀)).2 ⟨swapO 𝒪, rfl⟩]
  exact Homothetic.refl _

include hπ in
theorem pi_ne_zero : algebraMap 𝒪 K₀ π ≠ 0 := by
  intro h
  exact hπ.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K₀)).1 h)

def piU : K₀ˣ := Units.mk0 (algebraMap 𝒪 K₀ π) (pi_ne_zero 𝒪 π hπ K₀)

theorem act_scalarGL (c : K₀ˣ) (v : Vertex 𝒪 K₀) : Vertex.act (scalarGL c) v = v := by
  rw [← BruhatTits.gl_smul_def, ← BruhatTits.scalar_eq_scalarGL]
  exact BruhatTits.scalar_smul_vertex c v

def wrev : Matrix.GeneralLinearGroup (Fin 2) K₀ := g₁ * swap 𝒪 K₀

theorem act_wrev_s₀ : Vertex.act (wrev 𝒪 K₀ g₁) (s₀ 𝒪 K₀) = s₁ 𝒪 K₀ g₁ := by
  unfold wrev s₁; rw [Vertex.act_mul, act_swap_s₀]

include hπ hg₁ in
theorem act_wrev_s₁ : Vertex.act (wrev 𝒪 K₀ g₁) (s₁ 𝒪 K₀ g₁) = s₀ 𝒪 K₀ := by
  unfold wrev s₁
  have key : g₁ * swap 𝒪 K₀ * g₁ = scalarGL (piU 𝒪 π hπ K₀) * swap 𝒪 K₀ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, swap_val, hg₁, scalarGL_coe]
    have : ((piU 𝒪 π hπ K₀ : K₀ˣ) : K₀) = algebraMap 𝒪 K₀ π := rfl
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail, Matrix.smul_apply, this,
        Algebra.algebraMap_eq_smul_one]
  show Vertex.act (g₁ * swap 𝒪 K₀) (Vertex.act g₁ (stdVertex 𝒪 K₀)) = stdVertex 𝒪 K₀
  rw [← Vertex.act_mul, key, Vertex.act_mul, act_swap_s₀, act_scalarGL]

include hπ hg₁ in
theorem Sset_wrev : Sset 𝒪 K₀ g₁ (wrev 𝒪 K₀ g₁) :=
  Or.inr ⟨act_wrev_s₀ 𝒪 K₀ g₁, act_wrev_s₁ 𝒪 π hπ K₀ g₁ hg₁⟩

end Comb

section Rings
variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ)

abbrev An : Type := (chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})

abbrev Vn : Type := chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}

abbrev xiq : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)

abbrev etaq : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)

theorem isNilpotent_xiq_mul_etaq : IsNilpotent (xiq 𝒪 π r n * etaq 𝒪 π r n) := by
  refine ⟨n + 1, ?_⟩
  rw [← map_mul, chartERing.ξ_mul_η, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

end Rings

end LevelSep

open LevelSep in
theorem _root_.P2MW.S_CerednikDrinfeld_FormalOmega_isSeparated_of_mumfordGlueLaws.solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀))) (n : ℕ)
    (Z : Scheme.{0})
    (zb : Z ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (ζ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀), Spec (CommRingCat.of ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) ⟶ Z)
    (ζ_over : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀),
    ζ h ≫ zb ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))))
    (ζ_isOpenImmersion : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀), IsOpenImmersion (ζ h))
    (ζ_cover : ∃ S : Finset (Matrix.GeneralLinearGroup (Fin 2) K₀), ∀ z : Z, ∃ h ∈ S, z ∈ Set.range (ζ h).base)
    (ζ_inv : ∀ (g h : Matrix.GeneralLinearGroup (Fin 2) K₀), Matrix.ProjGenLinGroup.mk g ∈ N → ζ (g * h) = ζ h)
    (ι : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}))
    (ι_ξ : ι (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) = Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))
    (ι_η : ι (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)) * Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r) = algebraMap 𝒪 (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) π)
    (ι_isLocalization : @IsLocalization.Away ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) _ (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) _ ι.toRingHom.toAlgebra)
    (τ : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀), (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) ≃ₐ[𝒪] (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}))
    (τ_spec : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀), Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) → ∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
    (y : (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
              (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {((y.comp (τ g).toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {((y.comp (τ g).toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
              (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d')
    (α : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀), ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ≃ₐ[𝒪] ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
    (α_spec : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀), (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) →
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
    (xq : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {(((xq.comp (α g).toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (((xq.comp (α g).toAlgHom).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d')
    (ζ_edge : ∀ (h g : Matrix.GeneralLinearGroup (Fin 2) K₀), (Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act g (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act g (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀)) →
    ζ (h * g) = Spec.map (CommRingCat.ofHom (α g).toAlgHom.toRingHom) ≫ ζ h)
    (ζ_vertex : ∀ (h g : Matrix.GeneralLinearGroup (Fin 2) K₀), Vertex.act g (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) →
    Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ζ (h * g) =
      Spec.map (CommRingCat.ofHom (τ g).toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ζ h)
    (ζ_preimage_le : ∀ (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀),
    (∀ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N →
      ¬ ((Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
         (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀)))) →
    (ζ h') ⁻¹ᵁ (@Scheme.Hom.opensRange _ _ (ζ h) (ζ_isOpenImmersion h)) ≤
      (⨆ (_ : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
          (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨ Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))),
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (chartERing.ξ 𝒪 π r))) ⊔
      (⨆ (_ : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
          (Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))),
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (chartERing.η 𝒪 π r)))) :
    IsSeparated zb := by
  classical
  haveI hζoi : ∀ h, IsOpenImmersion (ζ h) := ζ_isOpenImmersion

  let q : Z ⟶ Spec (CommRingCat.of 𝒪) :=
    zb ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
  have hq : ∀ h, ζ h ≫ q = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (An 𝒪 π r n))) := fun h => ζ_over h
  suffices hsep : IsSeparated q by
    exact IsSeparated.of_comp zb (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))

  haveI hιoi : IsOpenImmersion (Spec.map (CommRingCat.ofHom ι.toRingHom)) :=
    isOpenImmersion_spec_of_away ι.toRingHom (xiq 𝒪 π r n) ι_isLocalization
  have hιrange := range_spec_of_away ι.toRingHom (xiq 𝒪 π r n) ι_isLocalization

  have hD : PrimeSpectrum.basicOpen (xiq 𝒪 π r n) ⊓ PrimeSpectrum.basicOpen (etaq 𝒪 π r n) = ⊥ :=
    basicOpen_inf_eq_bot_of_isNilpotent (isNilpotent_xiq_mul_etaq 𝒪 π r n)

  have chartEq : ∀ (h h'' g u : Matrix.GeneralLinearGroup (Fin 2) K₀), Matrix.ProjGenLinGroup.mk g ∈ N →
      Sset 𝒪 K₀ g₁ u → Vertex.act h'' (s₀ 𝒪 K₀) = Vertex.act (g * h * u) (s₀ 𝒪 K₀) →
      Vertex.act ((g * h * u)⁻¹ * h'') (s₀ 𝒪 K₀) = s₀ 𝒪 K₀ ∧
      Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ ζ h'' =
        Spec.map (CommRingCat.ofHom (τ ((g * h * u)⁻¹ * h'')).toAlgHom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom ι.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (α u).toAlgHom.toRingHom) ≫ ζ h := by
    intro h h'' g u hg hu hs
    have hc₀ : Vertex.act ((g * h * u)⁻¹ * h'') (s₀ 𝒪 K₀) = s₀ 𝒪 K₀ := by
      rw [Vertex.act_mul, hs, ← Vertex.act_mul (g * h * u)⁻¹ (g * h * u), inv_mul_cancel, Vertex.act_one]
    refine ⟨hc₀, ?_⟩
    have e1 : h'' = g * (h * u * ((g * h * u)⁻¹ * h'')) := by group
    conv_lhs => rw [e1]
    rw [ζ_inv g _ hg, ζ_vertex (h * u) _ hc₀, ζ_edge h u hu]

  have nonfix : ∀ (h h' v g u c : Matrix.GeneralLinearGroup (Fin 2) K₀), Sset 𝒪 K₀ g₁ u → Sset 𝒪 K₀ g₁ v →
      h' * v = g * h * u * c → Vertex.act c (s₀ 𝒪 K₀) = s₀ 𝒪 K₀ → Vertex.act c (s₁ 𝒪 K₀ g₁) = s₁ 𝒪 K₀ g₁ →
      SameEdge 𝒪 K₀ g₁ h' (g * h) := by
    intro h h' v g u c hu hv he hc0 hc1
    have : h' = g * h * (u * c * v⁻¹) := by
      calc h' = h' * v * v⁻¹ := by group
        _ = g * h * u * c * v⁻¹ := by rw [he]
        _ = g * h * (u * c * v⁻¹) := by group
    rw [this]
    exact sameEdge_mul_of_Sset 𝒪 K₀ g₁
      (Sset_mul 𝒪 K₀ g₁ (Sset_mul 𝒪 K₀ g₁ hu (Or.inl ⟨hc0, hc1⟩)) (Sset_inv 𝒪 K₀ g₁ hv)) (g * h)

  have piece : ∀ (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (ψ κ : An 𝒪 π r n →ₐ[𝒪] Vn 𝒪 π r n)
      (W : (Spec (CommRingCat.of (An 𝒪 π r n))).Opens)
      [IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom))],
      Set.range (Spec.map (CommRingCat.ofHom ψ.toRingHom)) = (W : Set _) →
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ζ h' = Spec.map (CommRingCat.ofHom κ.toRingHom) ≫ ζ h →
      κ.range ⊔ ψ.range = ⊤ →
      IsClosedImmersion (((pullback.snd (ζ h) (ζ h')) ⁻¹ᵁ W).ι ≫ pullback.mapDesc (ζ h) (ζ h') q) := by
    intro h h' ψ κ W _ hrange hjk hsup
    refine isClosedImmersion_ι_comp_mapDesc (ζ h) (ζ h') q (Spec.map (CommRingCat.ofHom ψ.toRingHom))
      (Spec.map (CommRingCat.ofHom κ.toRingHom)) hjk W (Opens.ext hrange) ?_
    exact isClosedImmersion_lift_of_range_sup_range_eq_top (ζ h ≫ q) (ζ h' ≫ q) (hq h) (hq h') κ ψ hsup _

  let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers (Matrix.GeneralLinearGroup (Fin 2) K₀)
      (fun _ => Spec (CommRingCat.of (An 𝒪 π r n))) ζ
      (fun z => by
        obtain ⟨S, hS⟩ := ζ_cover
        obtain ⟨h, -, y, hy⟩ := hS z
        exact ⟨h, y, hy⟩)
      (fun h => hζoi h)
  suffices pair : ∀ h h' : Matrix.GeneralLinearGroup (Fin 2) K₀,
      IsClosedImmersion (pullback.mapDesc (ζ h) (ζ h') q) by
    exact AlgebraicGeometry.IsSeparated.of_isClosedImmersion_mapDesc_openCover q 𝒰 (fun h h' => pair h h')
  intro h h'
  by_cases hA : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ SameEdge 𝒪 K₀ g₁ h' (g * h)
  ·
    obtain ⟨g, hg, hSE⟩ := hA
    have hs : Sset 𝒪 K₀ g₁ ((g * h)⁻¹ * h') := by
      rcases hSE with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl
          ⟨by rw [Vertex.act_mul, a, ← Vertex.act_mul (g * h)⁻¹ (g * h), inv_mul_cancel, Vertex.act_one],
           by rw [Vertex.act_mul, b, ← Vertex.act_mul (g * h)⁻¹ (g * h), inv_mul_cancel, Vertex.act_one]⟩
      · exact Or.inr
          ⟨by rw [Vertex.act_mul, a, ← Vertex.act_mul (g * h)⁻¹ (g * h), inv_mul_cancel, Vertex.act_one],
           by rw [Vertex.act_mul, b, ← Vertex.act_mul (g * h)⁻¹ (g * h), inv_mul_cancel, Vertex.act_one]⟩
    haveI : IsSeparated (ζ h ≫ q) := by rw [hq h]; infer_instance
    refine isClosedImmersion_mapDesc_of_eq_comp (ζ h) (ζ h') q
      (Spec.map (CommRingCat.ofHom (α ((g * h)⁻¹ * h')).toAlgHom.toRingHom)) ?_
    calc ζ h' = ζ (g * (h * ((g * h)⁻¹ * h'))) := by congr 1; group
      _ = ζ (h * ((g * h)⁻¹ * h')) := ζ_inv g _ hg
      _ = _ := ζ_edge h _ hs
  ·
    have hB : ∀ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N →
        ¬ SameEdge 𝒪 K₀ g₁ h' (g * h) := fun g hg hSE => hA ⟨g, hg, hSE⟩
    have hle := ζ_preimage_le h h' hB
    have hmem : ∀ p : ↑(pullback (ζ h) (ζ h')),
        (pullback.snd (ζ h) (ζ h')) p ∈ (ζ h') ⁻¹ᵁ (ζ h).opensRange := by
      intro p
      show (pullback.snd (ζ h) (ζ h')) p ∈ (((ζ h') ⁻¹ᵁ (ζ h).opensRange) : Set _)
      rw [← IsOpenImmersion.range_pullbackSnd (ζ h) (ζ h')]
      exact ⟨p, rfl⟩
    have hsnd : pullback.mapDesc (ζ h) (ζ h') q ≫ pullback.snd (ζ h ≫ q) (ζ h' ≫ q) = pullback.snd (ζ h) (ζ h') := by
      simp only [pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id]
    have hpre : ∀ W, pullback.mapDesc (ζ h) (ζ h') q ⁻¹ᵁ (pullback.snd (ζ h ≫ q) (ζ h' ≫ q) ⁻¹ᵁ W) =
        pullback.snd (ζ h) (ζ h') ⁻¹ᵁ W := by
      intro W; rw [← Scheme.Hom.comp_preimage, hsnd]
    refine isClosedImmersion_of_preimage_pair (pullback.mapDesc (ζ h) (ζ h') q)
      (pullback.snd (ζ h ≫ q) (ζ h' ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen (xiq 𝒪 π r n))
      (pullback.snd (ζ h ≫ q) (ζ h' ≫ q) ⁻¹ᵁ PrimeSpectrum.basicOpen (etaq 𝒪 π r n))
      (disjoint_preimage _ hD) ?_ ?_ ?_
    ·
      rw [hpre, hpre, eq_top_iff]
      rintro p -
      have hsub : (ζ h') ⁻¹ᵁ (ζ h).opensRange ≤
          PrimeSpectrum.basicOpen (xiq 𝒪 π r n) ⊔ PrimeSpectrum.basicOpen (etaq 𝒪 π r n) :=
        hle.trans (sup_le_sup (iSup_le fun _ => le_rfl) (iSup_le fun _ => le_rfl))
      have h2 := hsub (hmem p)
      exact Opens.mem_sup.2 ((Opens.mem_sup.1 h2).imp (fun e => e) (fun e => e))
    ·
      rw [hpre]
      by_cases hP : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
          (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨
            Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))
      · obtain ⟨g, hg, hδ⟩ := hP
        obtain ⟨u, hu, hs⟩ : ∃ u, Sset 𝒪 K₀ g₁ u ∧
            Vertex.act h' (s₀ 𝒪 K₀) = Vertex.act (g * h * u) (s₀ 𝒪 K₀) := by
          rcases hδ with h0 | h1
          · exact ⟨1, Sset_one 𝒪 K₀ g₁, by rw [mul_one]; exact h0⟩
          · exact ⟨wrev 𝒪 K₀ g₁, Sset_wrev 𝒪 π hπ K₀ g₁ hg₁, by rw [Vertex.act_mul (g * h), act_wrev_s₀]; exact h1⟩
        obtain ⟨hc₀, heq⟩ := chartEq h h' g u hg hu hs
        have hc₁ : Vertex.act ((g * h * u)⁻¹ * h') (s₁ 𝒪 K₀ g₁) ≠ s₁ 𝒪 K₀ g₁ := fun hc₁ =>
          hB g hg (nonfix h h' 1 g u ((g * h * u)⁻¹ * h') hu (Sset_one 𝒪 K₀ g₁) (by group) hc₀ hc₁)
        have hov := CerednikDrinfeld.FormalOmega.range_sup_range_comp_eq_top_of_isPullback_chartVRing 𝒪 hdvr π hπ
          hres K₀ g₁ hg₁ n ι ι_ξ ι_η ((g * h * u)⁻¹ * h') hc₀ hc₁ (τ ((g * h * u)⁻¹ * h')) (τ_spec _ hc₀)
        refine piece h h' ι (((τ ((g * h * u)⁻¹ * h')).toAlgHom.comp ι).comp (α u).toAlgHom)
          (PrimeSpectrum.basicOpen (xiq 𝒪 π r n)) hιrange ?_ ?_
        · rw [heq]
          simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp,
            Category.assoc]
        · rw [range_comp_algEquiv, sup_comm]
          exact hov
      · haveI : IsEmpty (Scheme.Opens.toScheme ((pullback.snd (ζ h) (ζ h')) ⁻¹ᵁ PrimeSpectrum.basicOpen (xiq 𝒪 π r n))) := by
          refine ⟨fun x => ?_⟩
          have h1 : (pullback.snd (ζ h) (ζ h')) x.1 ∈ PrimeSpectrum.basicOpen (xiq 𝒪 π r n) := x.2
          have hsub : (ζ h') ⁻¹ᵁ (ζ h).opensRange ≤ PrimeSpectrum.basicOpen (etaq 𝒪 π r n) :=
            hle.trans (sup_le (iSup_le fun hp => (hP hp).elim) (iSup_le fun _ => le_rfl))
          have h3 := hsub (hmem x.1)
          have : (pullback.snd (ζ h) (ζ h')) x.1 ∈ (⊥ : (Spec (CommRingCat.of (An 𝒪 π r n))).Opens) :=
            hD ▸ (show _ ∈ PrimeSpectrum.basicOpen (xiq 𝒪 π r n) ⊓ PrimeSpectrum.basicOpen (etaq 𝒪 π r n) from ⟨h1, h3⟩)
          exact this
        infer_instance
    ·
      rw [hpre]
      by_cases hP : ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
          (Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨
            Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))
      · obtain ⟨g, hg, hδ⟩ := hP
        have hw : Vertex.act (h' * wrev 𝒪 K₀ g₁) (s₀ 𝒪 K₀) = Vertex.act h' (s₁ 𝒪 K₀ g₁) := by
          rw [Vertex.act_mul, act_wrev_s₀]
        obtain ⟨u, hu, hs⟩ : ∃ u, Sset 𝒪 K₀ g₁ u ∧
            Vertex.act (h' * wrev 𝒪 K₀ g₁) (s₀ 𝒪 K₀) = Vertex.act (g * h * u) (s₀ 𝒪 K₀) := by
          rcases hδ with h0 | h1
          · exact ⟨1, Sset_one 𝒪 K₀ g₁, by rw [hw, mul_one]; exact h0⟩
          · exact ⟨wrev 𝒪 K₀ g₁, Sset_wrev 𝒪 π hπ K₀ g₁ hg₁, by
              rw [hw, Vertex.act_mul (g * h), act_wrev_s₀]; exact h1⟩
        obtain ⟨hc₀, heq⟩ := chartEq h (h' * wrev 𝒪 K₀ g₁) g u hg hu hs
        have hc₁ : Vertex.act ((g * h * u)⁻¹ * (h' * wrev 𝒪 K₀ g₁)) (s₁ 𝒪 K₀ g₁) ≠ s₁ 𝒪 K₀ g₁ := fun hc₁ =>
          hB g hg (nonfix h h' (wrev 𝒪 K₀ g₁) g u ((g * h * u)⁻¹ * (h' * wrev 𝒪 K₀ g₁)) hu
            (Sset_wrev 𝒪 π hπ K₀ g₁ hg₁) (by group) hc₀ hc₁)
        have hov := CerednikDrinfeld.FormalOmega.range_sup_range_comp_eq_top_of_isPullback_chartVRing 𝒪 hdvr π hπ
          hres K₀ g₁ hg₁ n ι ι_ξ ι_η ((g * h * u)⁻¹ * (h' * wrev 𝒪 K₀ g₁)) hc₀ hc₁
          (τ ((g * h * u)⁻¹ * (h' * wrev 𝒪 K₀ g₁))) (τ_spec _ hc₀)

        have hassoc := (CerednikDrinfeld.FormalOmega.associated_algEquiv_chartERing_xi_eta_of_isPullback 𝒪 hdvr π hπ
          hres K₀ g₁ hg₁ (wrev 𝒪 K₀ g₁) n (α (wrev 𝒪 K₀ g₁)) (α_spec _ (Sset_wrev 𝒪 π hπ K₀ g₁ hg₁))).2
          ⟨act_wrev_s₀ 𝒪 K₀ g₁, act_wrev_s₁ 𝒪 π hπ K₀ g₁ hg₁⟩
        haveI hαiso := isIso_spec_algEquiv (α (wrev 𝒪 K₀ g₁))
        have hψ : Spec.map (CommRingCat.ofHom (ι.comp (α (wrev 𝒪 K₀ g₁)).toAlgHom).toRingHom) =
            Spec.map (CommRingCat.ofHom ι.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (α (wrev 𝒪 K₀ g₁)).toAlgHom.toRingHom) := by
          simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp]
        haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (ι.comp (α (wrev 𝒪 K₀ g₁)).toAlgHom).toRingHom)) := by
          rw [hψ]; infer_instance
        refine piece h h' (ι.comp (α (wrev 𝒪 K₀ g₁)).toAlgHom)
          (((τ ((g * h * u)⁻¹ * (h' * wrev 𝒪 K₀ g₁))).toAlgHom.comp ι).comp (α u).toAlgHom)
          (PrimeSpectrum.basicOpen (etaq 𝒪 π r n)) ?_ ?_ ?_
        · have e1 : PrimeSpectrum.basicOpen (etaq 𝒪 π r n) =
              PrimeSpectrum.basicOpen ((α (wrev 𝒪 K₀ g₁)).symm (xiq 𝒪 π r n)) :=
            basicOpen_eq_of_associated (by
              have := hassoc.2.map (α (wrev 𝒪 K₀ g₁)).symm
              rwa [AlgEquiv.symm_apply_apply] at this)
          rw [e1]
          exact range_spec_comp_algEquiv ι (α (wrev 𝒪 K₀ g₁)) (xiq 𝒪 π r n) hιrange
        · rw [hψ, Category.assoc, ← ζ_edge h' (wrev 𝒪 K₀ g₁) (Sset_wrev 𝒪 π hπ K₀ g₁ hg₁), heq]
          simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp,
            Category.assoc]
        · rw [range_comp_algEquiv, range_comp_algEquiv, sup_comm]
          exact hov
      · haveI : IsEmpty (Scheme.Opens.toScheme ((pullback.snd (ζ h) (ζ h')) ⁻¹ᵁ PrimeSpectrum.basicOpen (etaq 𝒪 π r n))) := by
          refine ⟨fun x => ?_⟩
          have h1 : (pullback.snd (ζ h) (ζ h')) x.1 ∈ PrimeSpectrum.basicOpen (etaq 𝒪 π r n) := x.2
          have hsub : (ζ h') ⁻¹ᵁ (ζ h).opensRange ≤ PrimeSpectrum.basicOpen (xiq 𝒪 π r n) :=
            hle.trans (sup_le (iSup_le fun _ => le_rfl) (iSup_le fun hp => (hP hp).elim))
          have h3 := hsub (hmem x.1)
          have : (pullback.snd (ζ h) (ζ h')) x.1 ∈ (⊥ : (Spec (CommRingCat.of (An 𝒪 π r n))).Opens) :=
            hD ▸ (show _ ∈ PrimeSpectrum.basicOpen (xiq 𝒪 π r n) ⊓ PrimeSpectrum.basicOpen (etaq 𝒪 π r n) from ⟨h3, h1⟩)
          exact this
        infer_instance

end

end S_CerednikDrinfeld_FormalOmega_isSeparated_of_mumfordGlueLaws
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_isSeparated_of_mumfordGlueLaws (solution)
