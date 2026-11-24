-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_etaleChart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:37.434872+00:00
-- url     : https://prove2.me/submissions/03ec5cda-6f3d-43e4-8dc7-d7fda6f291c3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem opens_op_hom_ext {X : Scheme.{u}} {A B : (X.Opens)ᵒᵖ} (f g : A ⟶ B) : f = g := by
  apply Quiver.Hom.unop_inj
  apply Subsingleton.elim
private theorem presheaf_map_eq {X : Scheme.{u}} {A B : (X.Opens)ᵒᵖ} (f g : A ⟶ B) :
    X.presheaf.map f = X.presheaf.map g := by
  rw [opens_op_hom_ext f g]
private theorem appTop_homOfLE_comp_topIso_hom {X : Scheme.{u}} {V W : X.Opens} (h : W ≤ V) :
    Scheme.Hom.appTop (X.homOfLE h) ≫ W.topIso.hom =
      V.topIso.hom ≫ X.presheaf.map (homOfLE h).op := by
  simp
  exact (X.presheaf.map_comp _ _).symm.trans
    ((presheaf_map_eq _ _).trans (X.presheaf.map_comp _ _))
private theorem smooth_ΓSpecIso_inv_comp_appTop {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (V : X.Opens)
    (hV : IsAffineOpen V) :
    RingHom.Smooth (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
  have : IsAffine V.toScheme := hV
  have hfac : V.toScheme.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p)) =
        V.ι ≫ p := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have h3 := congrArg
    (fun f : V.toScheme ⟶ Spec (CommRingCat.of k) => V.toScheme.isoSpec.inv ≫ f) hfac
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h3
  have h2 : AlgebraicGeometry.Smooth
      (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
    rw [h3]
    infer_instance
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp h2
private theorem exists_mem_basicOpen_of_span_eq_top {X : Scheme.{u}} {U : X.Opens}
    (x : X) (hx : x ∈ U) (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤) :
    ∃ t ∈ s, x ∈ X.basicOpen t := by
  by_contra hcon
  push Not at hcon
  have : IsLocalRing (X.presheaf.stalk x) := inferInstance
  have hnu : ∀ t ∈ s, t ∈ Ideal.comap (X.presheaf.germ U x hx).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
    intro t ht
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    refine hcon t ht ((X.mem_basicOpen t x hx).mpr ?_)
    exact hunit
  have hle := Ideal.span_le.mpr hnu
  rw [hs] at hle
  have h1 := hle (Submodule.mem_top : (1 : Γ(X, U)) ∈ ⊤)
  rw [Ideal.mem_comap, map_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
    ((Ideal.eq_top_iff_one _).mpr h1)
private theorem exists_etale_eval₂Hom_of_submersivePresentation {k S : Type u} [CommRing k] [CommRing S] [Algebra k S]
    {ι σ : Type} [Finite ι] [Finite σ] (P : Algebra.SubmersivePresentation k S ι σ) :
    ∃ (n : ℕ) (v : ULift.{u} (Fin n) → S),
      RingHom.Etale (MvPolynomial.eval₂Hom (algebraMap k S) v) := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  obtain ⟨n, ⟨g0⟩⟩ := Finite.exists_equiv_fin ((Set.range P.map)ᶜ : Set ι)
  obtain ⟨e, he⟩ : ∃ e : σ ⊕ ULift.{u} (Fin n) ≃ ι, ∀ s, e (Sum.inl s) = P.map s :=
    ⟨(Equiv.sumCongr (Equiv.ofInjective P.map P.map_inj)
        ((g0.trans (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).symm).symm)).trans
          (Equiv.Set.sumCompl (Set.range P.map)), fun s => rfl⟩
  refine ⟨n, fun t => P.val (e (Sum.inr t)), ?_⟩
  let : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) S :=
    (MvPolynomial.eval₂Hom (algebraMap k S) fun t => P.val (e (Sum.inr t))).toAlgebra
  have halg : ∀ z : MvPolynomial (ULift.{u} (Fin n)) k,
      algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) S z =
        MvPolynomial.eval₂Hom (algebraMap k S) (fun t => P.val (e (Sum.inr t))) z := fun _ => rfl
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) S := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [halg]
    simp
  obtain ⟨Φ, hΦl, hΦr, hΦC⟩ :
      ∃ Φ : MvPolynomial ι k →+* MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k),
        (∀ s, Φ (MvPolynomial.X (e (Sum.inl s))) = MvPolynomial.X s) ∧
        (∀ t, Φ (MvPolynomial.X (e (Sum.inr t))) = MvPolynomial.C (MvPolynomial.X t)) ∧
        (∀ a : k, Φ (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a)) := by
    refine ⟨((MvPolynomial.aeval (fun i => Sum.elim (fun s => MvPolynomial.X s)
        (fun t => MvPolynomial.C (MvPolynomial.X t)) (e.symm i)) :
          MvPolynomial ι k →ₐ[k] MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k))).toRingHom,
      ?_, ?_, ?_⟩
    · intro s; simp
    · intro t; simp
    · intro a
      simp [MvPolynomial.algebraMap_eq,
        IsScalarTower.algebraMap_apply k (MvPolynomial (ULift.{u} (Fin n)) k)
          (MvPolynomial σ (MvPolynomial (ULift.{u} (Fin n)) k))]
  have hecases : ∀ i : ι, (∃ s, i = e (Sum.inl s)) ∨ (∃ t, i = e (Sum.inr t)) := by
    intro i
    rcases h : e.symm i with s | t
    · exact Or.inl ⟨s, by rw [← h, e.apply_symm_apply]⟩
    · exact Or.inr ⟨t, by rw [← h, e.apply_symm_apply]⟩
  have hΦsurj : Function.Surjective Φ := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C q =>
        induction q using MvPolynomial.induction_on with
        | C a => exact ⟨MvPolynomial.C a, hΦC a⟩
        | add q₁ q₂ h₁ h₂ =>
            obtain ⟨x, hx⟩ := h₁
            obtain ⟨y, hy⟩ := h₂
            exact ⟨x + y, by rw [map_add, hx, hy, ← map_add]⟩
        | mul_X q t hq =>
            obtain ⟨x, hx⟩ := hq
            exact ⟨x * MvPolynomial.X (e (Sum.inr t)), by rw [map_mul, hx, hΦr, ← map_mul]⟩
    | add z₁ z₂ h₁ h₂ =>
        obtain ⟨x, hx⟩ := h₁
        obtain ⟨y, hy⟩ := h₂
        exact ⟨x + y, by rw [map_add, hx, hy]⟩
    | mul_X z s hz =>
        obtain ⟨x, hx⟩ := hz
        exact ⟨x * MvPolynomial.X (e (Sum.inl s)), by rw [map_mul, hx, hΦl]⟩
  have hA : ∀ y : P.Ring, algebraMap P.Ring S y = MvPolynomial.aeval P.val y :=
    fun y => Algebra.Generators.algebraMap_apply _ y
  have hcompX : ∀ i : ι,
      (MvPolynomial.aeval (fun s => P.val (e (Sum.inl s)))) (Φ (MvPolynomial.X i)) = P.val i := by
    intro i
    rcases hecases i with ⟨s, rfl⟩ | ⟨t, rfl⟩
    · rw [hΦl, MvPolynomial.aeval_X]
    · rw [hΦr, MvPolynomial.aeval_C, halg]
      simp
  have hcomp : ∀ z : MvPolynomial ι k,
      (MvPolynomial.aeval (fun s => P.val (e (Sum.inl s)))) (Φ z) =
        MvPolynomial.aeval P.val z := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C a =>
        rw [hΦC, MvPolynomial.aeval_C, halg, MvPolynomial.aeval_C]
        simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | mul_X z i hz => simp only [map_mul, hz, hcompX, MvPolynomial.aeval_X]
  have hpdX : ∀ (s : σ) (i : ι),
      MvPolynomial.pderiv s (Φ (MvPolynomial.X i)) =
        Φ (MvPolynomial.pderiv (P.map s) (MvPolynomial.X i)) := by
    intro s i
    rcases hecases i with ⟨s', rfl⟩ | ⟨t, rfl⟩
    · rw [hΦl, he]
      by_cases hss : s = s'
      · subst hss
        rw [MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_self, map_one]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hss),
          MvPolynomial.pderiv_X_of_ne (fun hh => hss (P.map_inj hh).symm), map_zero]
    · have hne : e (Sum.inr t) ≠ P.map s := by
        intro hh
        have hsum : (Sum.inr t : σ ⊕ ULift.{u} (Fin n)) = Sum.inl s := by
          apply e.injective
          rw [hh, he]
        simp at hsum
      rw [hΦr, MvPolynomial.pderiv_C, MvPolynomial.pderiv_X_of_ne hne, map_zero]
  have hpd : ∀ (s : σ) (q : MvPolynomial ι k),
      MvPolynomial.pderiv s (Φ q) = Φ (MvPolynomial.pderiv (P.map s) q) := by
    intro s q
    induction q using MvPolynomial.induction_on with
    | C a => rw [hΦC, MvPolynomial.pderiv_C, MvPolynomial.pderiv_C, map_zero]
    | add q₁ q₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | mul_X q i hq => simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hq, hpdX]
  have hsurjW : Function.Surjective
      (MvPolynomial.aeval (R := MvPolynomial (ULift.{u} (Fin n)) k)
        (fun s => P.val (e (Sum.inl s)))) := by
    intro s
    exact ⟨Φ (P.σ' s), by rw [hcomp, P.aeval_val_σ']⟩
  let G : Algebra.Generators (MvPolynomial (ULift.{u} (Fin n)) k) S σ :=
    Algebra.Generators.ofSurjective (fun s => P.val (e (Sum.inl s))) hsurjW
  have hGval : G.val = fun s => P.val (e (Sum.inl s)) := rfl
  have hspanQ : Ideal.span (Set.range fun j => Φ (P.relation j)) = G.ker := by
    have h1 : (Set.range fun j => Φ (P.relation j)) = ⇑Φ '' Set.range P.relation :=
      Set.range_comp _ _
    have h2 : P.ker = Ideal.comap Φ G.ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val, Algebra.Generators.ker_eq_ker_aeval_val]
      ext z
      simp only [Ideal.mem_comap, RingHom.mem_ker, hGval, hcomp]
    rw [h1, ← Ideal.map_span, P.span_range_relation_eq_ker, h2,
      Ideal.map_comap_of_surjective Φ hΦsurj]
  obtain ⟨Q, hQmap, hQrel, hQalg⟩ :
      ∃ Q : Algebra.PreSubmersivePresentation (MvPolynomial (ULift.{u} (Fin n)) k) S σ σ,
        (∀ i, Q.map i = i) ∧ (∀ j, Q.relation j = Φ (P.relation j)) ∧
        (∀ z, algebraMap Q.Ring S z =
          MvPolynomial.aeval (fun s => P.val (e (Sum.inl s))) z) :=
    ⟨{ toGenerators := G
       relation := fun j => Φ (P.relation j)
       span_range_relation_eq_ker := hspanQ
       map := id
       map_inj := Function.injective_id },
      fun i => rfl, fun j => rfl, fun z => Algebra.Generators.algebraMap_apply G z⟩
  have hmat : ∀ i j, Q.jacobiMatrix i j = Φ (P.jacobiMatrix i j) := by
    intro i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hQmap, hQrel]
    exact hpd i (P.relation j)
  have hdet : Φ P.jacobiMatrix.det = Q.jacobiMatrix.det := by
    rw [RingHom.map_det Φ P.jacobiMatrix,
      show Q.jacobiMatrix = P.jacobiMatrix.map ⇑Φ from Matrix.ext fun i j => hmat i j]
    rfl
  have hjac : Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hA, hQalg, ← hdet, hcomp]
  have hunit : IsUnit Q.jacobian := by
    rw [hjac]
    exact P.jacobian_isUnit
  have : Algebra.IsStandardSmoothOfRelativeDimension 0
      (MvPolynomial (ULift.{u} (Fin n)) k) S := by
    refine ⟨σ, σ, inferInstance, inferInstance, ⟨Q, hunit⟩, ?_⟩
    simp [Algebra.Presentation.dimension]
  show Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) k) S
  infer_instance
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    ∃ (U : X.Opens) (m : ℕ), x ∈ U ∧ IsAffineOpen U ∧ Nonempty (EtaleChart p U m) := by
  classical
  obtain ⟨V, hxV, hV⟩ := Scheme.exists_isAffineOpen_mem (X := X) x
  have : IsAffine V.toScheme := hV
  set θV : CommRingCat.of k ⟶ Γ(V.toScheme, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p) with hθVdef
  set ψV : CommRingCat.of k ⟶ Γ(X, V) := θV ≫ V.topIso.hom with hψVdef
  have hsmV : RingHom.Smooth ψV.hom := by
    have h1 : RingHom.Smooth θV.hom := smooth_ΓSpecIso_inv_comp_appTop p V hV
    have h2 := RingHom.Smooth.respectsIso.left θV.hom V.topIso.commRingCatIsoToRingEquiv h1
    rw [hψVdef, CommRingCat.hom_comp]
    exact h2
  obtain ⟨s, hspan, hloc⟩ := RingHom.Smooth.locally_isStandardSmooth hsmV
  obtain ⟨t, hts, hxt⟩ := exists_mem_basicOpen_of_span_eq_top x hxV s hspan
  have hUV : X.basicOpen t ≤ V := X.basicOpen_le t
  have hU : IsAffineOpen (X.basicOpen t) := hV.basicOpen t
  have : IsAffine (X.basicOpen t).toScheme := hU
  set θU : CommRingCat.of k ⟶ Γ((X.basicOpen t).toScheme, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      Scheme.Hom.appTop ((X.basicOpen t).ι ≫ p) with hθUdef
  set ψU : CommRingCat.of k ⟶ Γ(X, X.basicOpen t) :=
    θU ≫ (X.basicOpen t).topIso.hom with hψUdef
  have hψUeq : ψU = ψV ≫ X.presheaf.map (homOfLE hUV).op := by
    have e1 : (X.basicOpen t).ι ≫ p = X.homOfLE hUV ≫ (V.ι ≫ p) := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [hψUdef, hθUdef, e1, Scheme.Hom.comp_appTop, hψVdef, hθVdef]
    simp only [Category.assoc]
    rw [appTop_homOfLE_comp_topIso_hom]
  have hstdψU : RingHom.IsStandardSmooth ψU.hom := by
    have := hV.isLocalization_basicOpen t
    have h1 := RingHom.isStandardSmooth_respectsIso.left
      ((algebraMap Γ(X, V) (Localization.Away t)).comp ψV.hom)
      (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(X, X.basicOpen t)).toRingEquiv (hloc t hts)
    have h2 : (((IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(X, X.basicOpen t)).toRingEquiv : Localization.Away t →+* Γ(X, X.basicOpen t)).comp
        ((algebraMap Γ(X, V) (Localization.Away t)).comp ψV.hom)) = ψU.hom := by
      rw [hψUeq, CommRingCat.hom_comp]
      apply RingHom.ext
      intro a
      exact (IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
        Γ(X, X.basicOpen t)).commutes (ψV.hom a)
    rw [← h2]
    exact h1
  have hstdθU : RingHom.IsStandardSmooth θU.hom := by
    have h1 := RingHom.isStandardSmooth_respectsIso.left ψU.hom
      (X.basicOpen t).topIso.symm.commRingCatIsoToRingEquiv hstdψU
    have h3 : θU = ψU ≫ (X.basicOpen t).topIso.inv := by
      rw [hψUdef, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 : (((X.basicOpen t).topIso.symm.commRingCatIsoToRingEquiv :
        Γ(X, X.basicOpen t) →+* Γ((X.basicOpen t).toScheme, ⊤)).comp ψU.hom) = θU.hom := by
      rw [h3, CommRingCat.hom_comp]
      rfl
    rw [← h2]
    exact h1
  let : Algebra (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤) := θU.hom.toAlgebra
  have hAlg : Algebra.IsStandardSmooth (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤) :=
    hstdθU
  obtain ⟨⟨ι, σ, hσ, hι, ⟨P⟩⟩⟩ := hAlg
  have : Finite σ := hσ
  have : Finite ι := hι
  obtain ⟨n, v, hv⟩ := exists_etale_eval₂Hom_of_submersivePresentation P
  set φ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) (CommRingCat.of k)) ⟶
      Γ((X.basicOpen t).toScheme, ⊤) :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (algebraMap (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)) v) with hφdef
  have : AlgebraicGeometry.Etale (Spec.map φ) :=
    AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr hv
  have hφC : CommRingCat.ofHom MvPolynomial.C ≫ φ = θU := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    show MvPolynomial.eval₂
        (algebraMap (CommRingCat.of k) Γ((X.basicOpen t).toScheme, ⊤)) v (MvPolynomial.C a)
      = θU.hom a
    exact MvPolynomial.eval₂_C _ _ a
  have hcs : ((X.basicOpen t).toScheme.isoSpec.hom ≫ Spec.map φ ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv) ≫
        affineSpaceFinToSpec k n = (X.basicOpen t).ι ≫ p := by
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, hφC,
      hθUdef]
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  exact ⟨X.basicOpen t, n, hxt, hU,
    ⟨⟨(X.basicOpen t).toScheme.isoSpec.hom ≫ Spec.map φ ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv, hcs, inferInstance⟩⟩⟩
end FunctorialResolution.EmbeddedResolution
