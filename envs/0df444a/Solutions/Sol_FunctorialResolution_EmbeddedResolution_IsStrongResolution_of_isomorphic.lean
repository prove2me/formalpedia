-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrongResolution.of_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:27.346902+00:00
-- url     : https://prove2.me/submissions/d90c177d-2fa2-4b00-bed2-59e0ab9b2294

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_Isomorphic_exists_lastObjIso
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_projectionToBase_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem mem_specMap_asIdeal {A B : CommRingCat.{u}} (ψ : A ⟶ B)
    (q : PrimeSpectrum B) (a : A) :
    a ∈ ((Spec.map ψ) q).asIdeal ↔ (ConcreteCategory.hom ψ) a ∈ q.asIdeal := Iff.rfl
private theorem vanishingIdeal_preimage_specMap {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsIso φ]
    (W : Set (PrimeSpectrum A)) :
    PrimeSpectrum.vanishingIdeal (⇑(Spec.map φ) ⁻¹' W)
      = Ideal.map (ConcreteCategory.hom φ) (PrimeSpectrum.vanishingIdeal W) := by
  have hinv : ∀ p : PrimeSpectrum (A : Type u),
      ((Spec.map φ) ((Spec.map (inv φ)) p) : PrimeSpectrum (A : Type u)) = p := by
    intro p
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro a
    constructor
    · intro hmem
      have h1 : (ConcreteCategory.hom (inv φ)) ((ConcreteCategory.hom φ) a) ∈ p.asIdeal :=
        (mem_specMap_asIdeal (inv φ) p _).mp ((mem_specMap_asIdeal φ _ a).mp hmem)
      rwa [IsIso.hom_inv_id_apply] at h1
    · intro hmem
      refine (mem_specMap_asIdeal φ _ a).mpr ?_
      refine (mem_specMap_asIdeal (inv φ) p _).mpr ?_
      rw [IsIso.hom_inv_id_apply]
      exact hmem
  apply le_antisymm
  · intro a ha
    rw [PrimeSpectrum.mem_vanishingIdeal] at ha
    have hmem : (ConcreteCategory.hom (inv φ)) a ∈ PrimeSpectrum.vanishingIdeal W := by
      rw [PrimeSpectrum.mem_vanishingIdeal]
      intro p hp
      have h1 : (Spec.map φ) ((Spec.map (inv φ)) p) ∈ W :=
        cast (congrArg (fun x : PrimeSpectrum (A : Type u) => x ∈ W) (hinv p)).symm hp
      exact (mem_specMap_asIdeal (inv φ) p a).mp (ha _ h1)
    have h3 : (ConcreteCategory.hom φ) ((ConcreteCategory.hom (inv φ)) a) = a := by
      rw [IsIso.inv_hom_id_apply]
    have h5 := Ideal.mem_map_of_mem (ConcreteCategory.hom φ) hmem
    rwa [h3] at h5
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [PrimeSpectrum.mem_vanishingIdeal] at ha
    rw [Ideal.mem_comap, PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    exact (mem_specMap_asIdeal φ q a).mp (ha _ hq)
private theorem vanishingIdeal_preimage_fromSpec_of_isIso {Y Y' : Scheme.{u}} (ψ : Y' ⟶ Y) [IsIso ψ]
    (T : Set Y) (U : Y.affineOpens) (hV : IsAffineOpen (ψ ⁻¹ᵁ (U : Y.Opens))) :
    PrimeSpectrum.vanishingIdeal (⇑hV.fromSpec ⁻¹' (⇑ψ ⁻¹' T))
      = Ideal.map (ConcreteCategory.hom (ψ.app (U : Y.Opens)))
          (PrimeSpectrum.vanishingIdeal (⇑U.2.fromSpec ⁻¹' T)) := by
  have : IsIso (ψ.app (U : Y.Opens)) := inferInstance
  have hU : IsAffineOpen (U : Y.Opens) := U.2
  have happ : ψ.appLE (U : Y.Opens) (ψ ⁻¹ᵁ (U : Y.Opens)) le_rfl = ψ.app (U : Y.Opens) := by
    simp [Scheme.Hom.appLE]
  have hsq : Spec.map (ψ.app (U : Y.Opens)) ≫ hU.fromSpec = hV.fromSpec ≫ ψ := by
    rw [← happ]
    exact AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec ψ hU hV le_rfl
  have hpt : ∀ z, ψ (hV.fromSpec z) = hU.fromSpec ((Spec.map (ψ.app (U : Y.Opens))) z) := by
    intro z
    have h := congrArg
      (fun m : Spec Γ(Y', ψ ⁻¹ᵁ (U : Y.Opens)) ⟶ Y => ⇑m z) hsq
    simpa using h.symm
  refine Eq.trans ?_ (vanishingIdeal_preimage_specMap (ψ.app (U : Y.Opens)) (⇑hU.fromSpec ⁻¹' T))
  exact congrArg PrimeSpectrum.vanishingIdeal
    (Set.ext fun z => iff_of_eq (congrArg (fun y => y ∈ T) (hpt z)))
private theorem map_mem_maximalIdeal_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) {a : R}
    (h : a ∈ IsLocalRing.maximalIdeal R) : e a ∈ IsLocalRing.maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
  intro hu
  exact h (by simpa using hu.map (e.symm : S →+* R))
private theorem isRegularParameterSystem_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : Fin n → R)
    (h : IsRegularParameterSystem R n x) :
    IsRegularParameterSystem S n (fun i => e (x i)) := by
  obtain ⟨hspan, hdim⟩ := h
  have hle : Ideal.span (Set.range fun i => e (x i)) ≤ IsLocalRing.maximalIdeal S := by
    rw [Ideal.span_le]
    rintro z ⟨i, rfl⟩
    show e (x i) ∈ IsLocalRing.maximalIdeal S
    refine map_mem_maximalIdeal_ringEquiv e ?_
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hge : IsLocalRing.maximalIdeal S ≤ Ideal.span (Set.range fun i => e (x i)) := by
    intro y hy
    have h1 : Ideal.span (Set.range x)
        ≤ Ideal.comap (e : R →+* S) (Ideal.span (Set.range fun i => e (x i))) := by
      rw [Ideal.span_le]
      rintro z ⟨i, rfl⟩
      simp only [SetLike.mem_coe, Ideal.mem_comap, RingHom.coe_coe]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h2 : e.symm y ∈ IsLocalRing.maximalIdeal R := map_mem_maximalIdeal_ringEquiv e.symm hy
    have h3 : e.symm y ∈ Ideal.span (Set.range x) := by rw [hspan]; exact h2
    have h4 := h1 h3
    rw [Ideal.mem_comap] at h4
    simpa using h4
  exact ⟨le_antisymm hle hge, hdim.trans (ringKrullDim_eq_of_ringEquiv e)⟩
private theorem isRegularParameterSystem_congr {R : Type u} [CommRing R] [IsLocalRing R]
    (n : ℕ) {x y : Fin n → R} (h : ∀ i, x i = y i) (hy : IsRegularParameterSystem R n y) :
    IsRegularParameterSystem R n x := by
  have hxy : x = y := funext h
  rw [hxy]
  exact hy
private theorem iso_hom_comp_projectionToBase_of_commute_blowupMorphism {X : Scheme.{u}} {B B' : SequenceOfBlowups X}
    (e : ∀ i : ℕ, i ≤ B.length → (B.schemeAt i ≅ B'.schemeAt i))
    (h0 : (e 0 (Nat.zero_le _)).hom ≫ B'.isoZero.hom = B.isoZero.hom)
    (hstep : ∀ i : ℕ, ∀ hi : i < B.length,
        (e (i + 1) hi).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hi.le).hom) :
    ∀ (i : ℕ) (hi : i ≤ B.length), (e i hi).hom ≫ B'.projectionToBase i = B.projectionToBase i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [B'.projectionToBase_zero, B.projectionToBase_zero]
    exact h0
  | succ n ih =>
    intro hi
    have hn : n < B.length := hi
    rw [B'.projectionToBase_succ, B.projectionToBase_succ, ← Category.assoc]
    show ((e (n + 1) hn).hom ≫ B'.transitionMapSucc n) ≫ B'.projectionToBase n
      = B.transitionMapSucc n ≫ B.projectionToBase n
    rw [hstep n hn, Category.assoc, ih hn.le]
private theorem mem_support_of_mem_support_comap {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (I : Z.IdealSheafData) {x : Y} (hx : x ∈ (I.comap g).support) : g x ∈ I.support := by
  have h := Scheme.IdealSheafData.support_comap I g
  rw [h] at hx
  exact hx
private theorem inv_mem_support_comap_of_iso {Y Z : Scheme.{u}} (g : Y ≅ Z) (I : Z.IdealSheafData)
    {x : Z} (hx : x ∈ I.support) : g.inv x ∈ (I.comap g.hom).support := by
  have hI : (I.comap g.hom).comap g.inv = I := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have hx' : x ∈ ((I.comap g.hom).comap g.inv).support := by rw [hI]; exact hx
  exact mem_support_of_mem_support_comap g.inv (I.comap g.hom) hx'
private theorem isIso_restrict_of_eq {Y Z : Scheme.{u}} {f₁ f₂ : Y ⟶ Z} (hf : f₁ = f₂)
    (U : Z.Opens) (h : IsIso (f₁ ∣_ U)) : IsIso (f₂ ∣_ U) := by
  subst hf
  exact h
private theorem isOpenMap_iso_hom {Y Z : Scheme.{u}} (g : Y ≅ Z) : IsOpenMap (⇑g.hom) :=
  (Scheme.homeoOfIso g).isOpenMap
private theorem isStrictNormalCrossingsDivisor_reducedInverseImage_iso_inv_comp {Y Y' X : Scheme.{u}} (g : Y ≅ Y') (p : Y ⟶ X)
    (S : TopologicalSpace.Closeds X) (hS : IsStrictNormalCrossingsDivisor (reducedInverseImage p S)) :
    IsStrictNormalCrossingsDivisor (reducedInverseImage (g.inv ≫ p) S) := by
  intro y'
  obtain ⟨hreg, U, hy, n, fs, J, hrsp, hideal⟩ := hS (g.inv.base y')
  have hsi : IsIso (g.inv.stalkMap y') := inferInstance
  have hV : IsAffineOpen (g.inv ⁻¹ᵁ (U : Y.Opens)) := U.2.preimage_of_isIso g.inv
  have he : ∀ t, (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv t
      = (ConcreteCategory.hom (g.inv.stalkMap y')) t := fun _ => rfl
  have hnat : ∀ s : Γ(Y, (U : Y.Opens)),
      (ConcreteCategory.hom (Y'.presheaf.germ (g.inv ⁻¹ᵁ (U : Y.Opens)) y' hy))
          ((ConcreteCategory.hom (g.inv.app (U : Y.Opens))) s)
        = (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv
            ((ConcreteCategory.hom (Y.presheaf.germ (U : Y.Opens) (g.inv.base y') hy)) s) := by
    intro s
    rw [he]
    simp
  refine ⟨?_, ⟨g.inv ⁻¹ᵁ (U : Y.Opens), hV⟩, hy, n,
    fun i => (ConcreteCategory.hom (g.inv.app (U : Y.Opens))) (fs i), J, ?_, ?_⟩
  · have := hreg
    exact IsRegularLocalRing.of_ringEquiv (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv
  · refine isRegularParameterSystem_congr n (fun i => hnat (fs i)) ?_
    exact isRegularParameterSystem_ringEquiv
      (asIso (g.inv.stalkMap y')).commRingCatIsoToRingEquiv n
      (fun i => (ConcreteCategory.hom
        (Y.presheaf.germ (U : Y.Opens) (g.inv.base y') hy)) (fs i)) hrsp
  · have h1 : (reducedInverseImage (g.inv ≫ p) S).ideal ⟨g.inv ⁻¹ᵁ (U : Y.Opens), hV⟩
        = PrimeSpectrum.vanishingIdeal
            (⇑hV.fromSpec ⁻¹' (⇑(g.inv ≫ p) ⁻¹' (S : Set X))) := by
      simp [reducedInverseImage, Scheme.IdealSheafData.vanishingIdeal_ideal]
    have h2 : (reducedInverseImage p S).ideal U
        = PrimeSpectrum.vanishingIdeal (⇑U.2.fromSpec ⁻¹' (⇑p ⁻¹' (S : Set X))) := by
      simp [reducedInverseImage, Scheme.IdealSheafData.vanishingIdeal_ideal]
    have hcomp : (⇑(g.inv ≫ p) ⁻¹' (S : Set X)) = ⇑g.inv ⁻¹' (⇑p ⁻¹' (S : Set X)) := by
      ext z
      simp
    rw [h1, hcomp, vanishingIdeal_preimage_fromSpec_of_isIso g.inv (⇑p ⁻¹' (S : Set X)) U hV, ← h2, hideal,
      Ideal.map_span]
    simp [map_prod]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace IsStrongResolution
theorem _root_.solution (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
    {B B' : SequenceOfBlowups X} (h : B.Isomorphic B') (hB : IsStrongResolution k X f B) :
    IsStrongResolution k X f B' := by
  obtain ⟨ε, hε⟩ := h.exists_lastObjIso
  obtain ⟨hs, hp, hiso, hd, hc, hsnc⟩ := hB
  have hmap : B'.lastStructMap = ε.inv ≫ B.lastStructMap := by
    rw [← hε, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have q1 : AlgebraicGeometry.Smooth (B'.lastStructMap ≫ f) := by
    have := hs
    rw [hmap, Category.assoc]
    infer_instance
  have q2 : AlgebraicGeometry.IsProper B'.lastStructMap := by
    have := hp
    rw [hmap]
    infer_instance
  have q3 : CategoryTheory.IsIso
      (AlgebraicGeometry.morphismRestrict B'.lastStructMap f.smoothLocus) := by
    have hres : IsIso (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus)) := inferInstance
    have hA : IsIso (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus) ≫ B'.lastStructMap ∣_ f.smoothLocus) := by
      have h0 : IsIso ((ε.hom ≫ B'.lastStructMap) ∣_ f.smoothLocus) :=
        isIso_restrict_of_eq hε.symm f.smoothLocus hiso
      rw [AlgebraicGeometry.morphismRestrict_comp] at h0
      exact h0
    exact IsIso.of_isIso_comp_left (ε.hom ∣_ (B'.lastStructMap ⁻¹ᵁ f.smoothLocus))
      (B'.lastStructMap ∣_ f.smoothLocus)
  have q4 : Dense (⇑B'.lastStructMap ⁻¹' (f.smoothLocus : Set X)) := by
    have hpre : ⇑B'.lastStructMap ⁻¹' (f.smoothLocus : Set X)
        = ⇑ε.inv ⁻¹' (⇑B.lastStructMap ⁻¹' (f.smoothLocus : Set X)) := by
      rw [hmap]
      ext x
      simp
    rw [hpre]
    exact hd.preimage (isOpenMap_iso_hom ε.symm)
  have q5 : B'.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X) := by
    obtain ⟨hL, eiso, h0, hstep, hcen⟩ := h
    intro i hi x hx
    have hi' : i < B.length := by omega
    have hy := inv_mem_support_comap_of_iso (eiso i hi'.le) (B'.center i) hx
    rw [hcen i hi'] at hy
    have hpt := hc i hi' _ hy
    have hkey : (eiso i hi'.le).hom ≫ B'.projectionToBase i = B.projectionToBase i :=
      iso_hom_comp_projectionToBase_of_commute_blowupMorphism eiso h0 hstep i hi'.le
    have hinv : (eiso i hi'.le).inv ≫ B.projectionToBase i = B'.projectionToBase i := by
      rw [← hkey, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have hval : B'.projectionToBase i x = B.projectionToBase i ((eiso i hi'.le).inv x) := by
      rw [← hinv]
      simp
    rw [hval]
    exact hpt
  have q6 : IsStrictNormalCrossingsDivisor (reducedInverseImage B'.lastStructMap (smoothLocusComplement f)) := by
    rw [hmap]
    exact isStrictNormalCrossingsDivisor_reducedInverseImage_iso_inv_comp ε B.lastStructMap (smoothLocusComplement f) hsnc
  exact ⟨q1, q2, q3, q4, q5, q6⟩
end IsStrongResolution
end FunctorialResolution.EmbeddedResolution
