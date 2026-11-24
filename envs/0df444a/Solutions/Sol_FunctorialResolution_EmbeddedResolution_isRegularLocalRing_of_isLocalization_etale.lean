-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRegularLocalRing_of_isLocalization_etale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:45.026809+00:00
-- url     : https://prove2.me/submissions/57fbcf5c-1de8-43e4-b744-9ac4fb6a3ec8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_flat_formallyUnramified
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_eq_of_flat_formallyUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
namespace FunctorialResolution.EmbeddedResolution
private theorem isRegularLocalRing_localization_coordPolynomialRing (k : Type u) [Field k] (m : ℕ)
    (p : Ideal (CoordPolynomialRing k m)) (hp : p.IsPrime) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have := hp
  infer_instance
private theorem isRegularLocalRing_and_ringKrullDim_eq_of_etale (P S : Type u) [CommRing P] [CommRing S] [Algebra P S]
    [Algebra.Etale P S] [IsNoetherianRing P]
    (hreg : ∀ (p : Ideal P) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A ∧
      ringKrullDim A = ringKrullDim (Localization.AtPrime (q.comap (algebraMap P S))) := by
  have : Algebra.FiniteType P S := inferInstance
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing P S
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing q.primeCompl A inferInstance
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A q
  let : Algebra P A := ((algebraMap S A).comp (algebraMap P S)).toAlgebra
  have : IsScalarTower P S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat P S := inferInstance
  have : Module.Flat S A := IsLocalization.flat A q.primeCompl
  have : Module.Flat P A := Module.Flat.trans P S A
  have : Algebra.FormallyUnramified P S := inferInstance
  have : Algebra.FormallyUnramified S A :=
    Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  have : Algebra.FormallyUnramified P A := Algebra.FormallyUnramified.comp P S A
  have : Algebra.EssFiniteType P S := inferInstance
  have : Algebra.EssFiniteType S A := Algebra.EssFiniteType.of_isLocalization A q.primeCompl
  have : Algebra.EssFiniteType P A := Algebra.EssFiniteType.comp P S A
  have hunits : ∀ y : (q.comap (algebraMap P S)).primeCompl, IsUnit (algebraMap P A (y : P)) := by
    rintro ⟨y, hy⟩
    have hy' : algebraMap P S y ∈ q.primeCompl := hy
    have h := IsLocalization.map_units A ⟨algebraMap P S y, hy'⟩
    rw [IsScalarTower.algebraMap_apply P S A]
    exact h
  let : Algebra (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    (IsLocalization.lift hunits).toAlgebra
  have : IsScalarTower P (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunits x).symm
  have : Module.Flat (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.comap (algebraMap P S)))
      (q.comap (algebraMap P S)).primeCompl A).mpr ‹_›
  have : Algebra.FormallyUnramified (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    Algebra.FormallyUnramified.localization_base (M := (q.comap (algebraMap P S)).primeCompl)
  have : Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    Algebra.EssFiniteType.of_comp P (Localization.AtPrime (q.comap (algebraMap P S))) A
  have : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap P S))) :=
    hreg _
  have : IsLocalHom (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A) := by
    constructor
    intro r hr
    obtain ⟨⟨x, s⟩, hx⟩ :=
      IsLocalization.surj (M := (q.comap (algebraMap P S)).primeCompl) r
    have hxA : algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A r
        * algebraMap P A (s : P) = algebraMap P A x := by
      have h := congrArg (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A) hx
      rw [map_mul] at h
      rw [IsScalarTower.algebraMap_apply P
            (Localization.AtPrime (q.comap (algebraMap P S))) A (s : P),
        IsScalarTower.algebraMap_apply P
            (Localization.AtPrime (q.comap (algebraMap P S))) A x]
      exact h
    have h2 : IsUnit (algebraMap P A x) := by
      rw [← hxA]
      exact hr.mul (hunits s)
    have h3 : IsUnit (algebraMap S A (algebraMap P S x)) := by
      rw [← IsScalarTower.algebraMap_apply P S A]
      exact h2
    have h4 : algebraMap P S x ∈ q.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff A q (algebraMap P S x)).mp h3
    have h5 : x ∈ (q.comap (algebraMap P S)).primeCompl := h4
    have h6 : IsUnit (algebraMap P (Localization.AtPrime (q.comap (algebraMap P S))) x) :=
      IsLocalization.map_units _ ⟨x, h5⟩
    rw [← hx] at h6
    exact (IsUnit.mul_iff.mp h6).1
  exact ⟨isRegularLocalRing_of_flat_formallyUnramified
      (Localization.AtPrime (q.comap (algebraMap P S))) A,
    ringKrullDim_eq_of_flat_formallyUnramified
      (Localization.AtPrime (q.comap (algebraMap P S))) A⟩
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A :=
  (isRegularLocalRing_and_ringKrullDim_eq_of_etale (CoordPolynomialRing k m) S
    (by intro p hp; exact isRegularLocalRing_localization_coordPolynomialRing k m p hp) q A).1
end FunctorialResolution.EmbeddedResolution
