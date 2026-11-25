-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isClopen_irreducibleComponent_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:21:51.256709+00:00
-- url     : https://prove2.me/submissions/8bcfdae0-b3ea-454b-bbab-3be22fbf602f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isDomain_stalk_of_smooth
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
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
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem eq_closure_of_mem_irreducibleComponents {α : Type*} [TopologicalSpace α]
    {V : Set α} (hVopen : IsOpen V) (hVirr : IsIrreducible V) {T : Set α}
    (hT : T ∈ irreducibleComponents α) {x : α} (hxV : x ∈ V) (hxT : x ∈ T) : T = closure V := by
  have hsub : T ⊆ closure V := by
    intro y hy
    rw [mem_closure_iff]
    intro o ho hyo
    obtain ⟨z, -, hzo, hzV⟩ := hT.1.2 o V ho hVopen ⟨y, hy, hyo⟩ ⟨x, hxT, hxV⟩
    exact ⟨z, hzo, hzV⟩
  exact le_antisymm hsub (hT.2 hVirr.closure hsub)
private theorem exists_isOpen_isIrreducible_of_unique_irreducibleComponent {α : Type*} [TopologicalSpace α]
    (hfin : (irreducibleComponents α).Finite) {T₀ : Set α} (hT₀ : IsIrreducible T₀) {z : α}
    (_hz : z ∈ T₀) (huniq : ∀ T ∈ irreducibleComponents α, z ∈ T → T = T₀) :
    ∃ W : Set α, IsOpen W ∧ IsIrreducible W ∧ z ∈ W := by
  have hSfin : Set.Finite {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T} :=
    Set.Finite.subset hfin (fun T hT => hT.1)
  have hScl : IsClosed (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T}) := by
    rw [Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion hSfin
      (fun T hT => isClosed_of_mem_irreducibleComponents _ hT.1)
  have hzW : z ∈ (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ := by
    intro hcon
    obtain ⟨T, hTS, hzT⟩ := hcon
    exact hTS.2 hzT
  have hWT : (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ ⊆ T₀ := by
    intro y hy
    have hc : irreducibleComponent y ∈ irreducibleComponents α :=
      irreducibleComponent_mem_irreducibleComponents y
    have hzc : z ∈ irreducibleComponent y := by
      by_contra hcon
      exact hy ⟨irreducibleComponent y, ⟨hc, hcon⟩, mem_irreducibleComponent⟩
    rw [← huniq _ hc hzc]
    exact mem_irreducibleComponent
  refine ⟨_, hScl.isOpen_compl, ⟨⟨z, hzW⟩, ?_⟩, hzW⟩
  intro u v hu hv hu' hv'
  obtain ⟨a, haW, hau⟩ := hu'
  obtain ⟨b, hbW, hbv⟩ := hv'
  obtain ⟨c, -, ⟨hcu, hcW⟩, hcv, -⟩ :=
    hT₀.2 (u ∩ (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ)
      (v ∩ (⋃₀ {T : Set α | T ∈ irreducibleComponents α ∧ z ∉ T})ᶜ)
      (hu.inter hScl.isOpen_compl) (hv.inter hScl.isOpen_compl)
      ⟨a, hWT haW, hau, haW⟩ ⟨b, hWT hbW, hbv, hbW⟩
  exact ⟨c, hcW, hcu, hcv⟩
private theorem exists_isOpen_isIrreducible_of_unique_minimal_prime_le {A : Type u} [CommRing A]
    [IsNoetherianRing A] (P : PrimeSpectrum A) (K : Ideal A) (hK : K.IsPrime)
    (hmin : ∀ q : Ideal A, q.IsPrime → q ≤ P.asIdeal → K ≤ q) :
    ∃ W : Set (PrimeSpectrum A), IsOpen W ∧ IsIrreducible W ∧ P ∈ W := by
  have hT₀irr : IsIrreducible (PrimeSpectrum.zeroLocus (K : Set A)) := by
    rw [PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime,
      PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hK.radical]
    exact hK
  have hPT₀ : P ∈ PrimeSpectrum.zeroLocus (K : Set A) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    exact fun a ha => hmin P.asIdeal P.isPrime le_rfl ha
  have hcomp : ∀ T ∈ irreducibleComponents (PrimeSpectrum A), P ∈ T →
      T = PrimeSpectrum.zeroLocus (K : Set A) := by
    intro T hT hPmem
    have hTcl : IsClosed T := isClosed_of_mem_irreducibleComponents _ hT
    have hq : (PrimeSpectrum.vanishingIdeal T).IsPrime :=
      PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hT.1
    have hTeq : PrimeSpectrum.zeroLocus ((PrimeSpectrum.vanishingIdeal T : Ideal A) : Set A)
        = T := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hTcl.closure_eq]
    have hqP : PrimeSpectrum.vanishingIdeal T ≤ P.asIdeal := fun a ha =>
      (PrimeSpectrum.mem_vanishingIdeal T a).mp ha P hPmem
    have hKq : K ≤ PrimeSpectrum.vanishingIdeal T := hmin _ hq hqP
    have hTsub : T ⊆ PrimeSpectrum.zeroLocus (K : Set A) := by
      rw [← hTeq]
      exact PrimeSpectrum.zeroLocus_anti_mono (SetLike.coe_subset_coe.mpr hKq)
    exact le_antisymm hTsub (hT.2 hT₀irr hTsub)
  have hfin : (irreducibleComponents (PrimeSpectrum A)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  exact exists_isOpen_isIrreducible_of_unique_irreducibleComponent hfin hT₀irr hPT₀ hcomp
private theorem finiteType_appTop_of_isAffineOpen_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (V : X.Opens)
    (hV : IsAffineOpen V) :
    RingHom.FiniteType (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
  have : IsAffine V.toScheme := hV
  have hfac : V.toScheme.isoSpec.hom ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))
        = V.ι ≫ p := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have h3 := congrArg
    (fun f : V.toScheme ⟶ Spec (CommRingCat.of k) => V.toScheme.isoSpec.inv ≫ f) hfac
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h3
  have h2 : AlgebraicGeometry.LocallyOfFiniteType
      (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop (V.ι ≫ p))) := by
    rw [h3]
    infer_instance
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp h2
private theorem isNoetherianRing_sections_of_isAffineOpen_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (V : X.Opens)
    (hV : IsAffineOpen V) : IsNoetherianRing ↥Γ(V.toScheme, ⊤) := by
  have hft := finiteType_appTop_of_isAffineOpen_of_smooth p V hV
  let _ : Algebra ↥(CommRingCat.of k) ↥Γ(V.toScheme, ⊤) :=
    (CommRingCat.Hom.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      Scheme.Hom.appTop (V.ι ≫ p))).toAlgebra
  have : Algebra.FiniteType ↥(CommRingCat.of k) ↥Γ(V.toScheme, ⊤) := hft
  have : IsNoetherianRing ↥(CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  exact Algebra.FiniteType.isNoetherianRing ↥(CommRingCat.of k) ↥Γ(V.toScheme, ⊤)
private theorem isDomain_localization_of_iso_spec {Y : Scheme.{u}} (R : CommRingCat.{u})
    (e : Y ≅ Spec R) (y : Y) (hdom : IsDomain ↥(Y.presheaf.stalk y)) :
    IsDomain (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) := by
  have := hdom
  have hp : (pointOfIsoSpec R e y).asIdeal.IsPrime := (pointOfIsoSpec R e y).isPrime
  have h2 : IsLocalization.AtPrime
      ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y))
      (pointOfIsoSpec R e y).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk ↥R (pointOfIsoSpec R e y)
  have e2 : Localization.AtPrime (pointOfIsoSpec R e y).asIdeal ≃+*
      ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y)) :=
    (IsLocalization.algEquiv (pointOfIsoSpec R e y).asIdeal.primeCompl
      (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)
      ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y))).toRingEquiv
  have h4 : IsIso (e.hom.stalkMap y) := inferInstance
  have e3 : ((Spec.structureSheaf ↥R).presheaf.stalk (pointOfIsoSpec R e y)) ≃+*
      ↥(Y.presheaf.stalk y) :=
    (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv
  exact (e2.trans e3).toMulEquiv.isDomain _
private theorem exists_isOpen_isIrreducible_of_iso_spec_of_isDomain_stalk {Y : Scheme.{u}} (R : CommRingCat.{u})
    [IsNoetherianRing ↥R] (e : Y ≅ Spec R) (y : Y)
    (hdom : IsDomain ↥(Y.presheaf.stalk y)) :
    ∃ V : Set Y, IsOpen V ∧ IsIrreducible V ∧ y ∈ V := by
  have hPp : (pointOfIsoSpec R e y).asIdeal.IsPrime := (pointOfIsoSpec R e y).isPrime
  have hdomL : IsDomain (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) :=
    isDomain_localization_of_iso_spec R e y hdom
  have hbot : (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)).IsPrime :=
    Ideal.isPrime_bot
  have hKp : (Ideal.comap
      (algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))
      (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))).IsPrime :=
    Ideal.comap_isPrime _ _
  have hmin : ∀ q : Ideal ↥R, q.IsPrime → q ≤ (pointOfIsoSpec R e y).asIdeal →
      Ideal.comap (algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))
        (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)) ≤ q := by
    intro q hq hqP a ha
    have h0 : algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) a = 0 := by
      simpa [Ideal.mem_comap, Submodule.mem_bot] using ha
    have h1 : algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) a
        = algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal) 0 := by
      rw [h0, map_zero]
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
      (pointOfIsoSpec R e y).asIdeal.primeCompl
      (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal)).mp h1
    rw [mul_zero] at hc
    have hmem : (c : ↥R) * a ∈ q := by
      rw [hc]
      exact q.zero_mem
    rcases hq.mem_or_mem hmem with h | h
    · exact absurd (hqP h) c.2
    · exact h
  obtain ⟨W, hWopen, hWirr, hPW⟩ :=
    exists_isOpen_isIrreducible_of_unique_minimal_prime_le (pointOfIsoSpec R e y)
      (Ideal.comap (algebraMap ↥R (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))
        (⊥ : Ideal (Localization.AtPrime (pointOfIsoSpec R e y).asIdeal))) hKp hmin
  refine ⟨(Scheme.homeoOfIso e).symm '' W,
    (Scheme.homeoOfIso e).symm.isOpenMap W hWopen,
    hWirr.image _ (Scheme.homeoOfIso e).symm.continuous.continuousOn,
    ⟨pointOfIsoSpec R e y, hPW, (Scheme.homeoOfIso e).symm_apply_apply y⟩⟩
private theorem exists_isOpen_isIrreducible_mem_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    ∃ V : Set X, IsOpen V ∧ IsIrreducible V ∧ x ∈ V := by
  obtain ⟨U, hxU, hU'⟩ := Scheme.exists_isAffineOpen_mem x
  have : IsAffine U.toScheme := hU'
  have hnoeth : IsNoetherianRing ↥Γ(U.toScheme, ⊤) := isNoetherianRing_sections_of_isAffineOpen_of_smooth p U hU'
  have hdomX : IsDomain ↥(X.presheaf.stalk x) := isDomain_stalk_of_smooth p x
  have hdomU : IsDomain ↥(U.toScheme.presheaf.stalk (⟨x, hxU⟩ : U)) :=
    (U.stalkIso (⟨x, hxU⟩ : U)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  obtain ⟨V, hVopen, hVirr, hyV⟩ :=
    exists_isOpen_isIrreducible_of_iso_spec_of_isDomain_stalk Γ(U.toScheme, ⊤) U.toScheme.isoSpec
      (⟨x, hxU⟩ : U) hdomU
  have hoe := U.ι.isOpenEmbedding
  exact ⟨U.ι.base '' V, hoe.isOpenMap V hVopen,
    hVirr.image _ hoe.continuous.continuousOn, ⟨(⟨x, hxU⟩ : U), hyV, rfl⟩⟩
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p)
    {T : Set ↥X} (hT : T ∈ irreducibleComponents ↥X) : IsClopen T := by
  have := hp
  have hclosed : IsClosed T := isClosed_of_mem_irreducibleComponents _ hT
  have hopen : IsOpen T := by
    rw [isOpen_iff_forall_mem_open]
    intro z hzT
    obtain ⟨W, hWopen, hWirr, hzW⟩ := exists_isOpen_isIrreducible_mem_of_smooth p z
    refine ⟨W, ?_, hWopen, hzW⟩
    rw [eq_closure_of_mem_irreducibleComponents hWopen hWirr hT hzW hzT]
    exact subset_closure
  exact ⟨hclosed, hopen⟩
end FunctorialResolution.EmbeddedResolution
