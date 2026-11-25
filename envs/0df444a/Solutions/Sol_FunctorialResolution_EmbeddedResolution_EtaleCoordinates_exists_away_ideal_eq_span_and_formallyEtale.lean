-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.exists_away_ideal_eq_span_and_formallyEtale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:23:07.909887+00:00
-- url     : https://prove2.me/submissions/fe62ef54-47e7-479d-b659-45d7263e51b3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealGeneratorsFromBase
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalNormalForm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_exists_away_ideal_eq_span_and_isUnit_det
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_det_basisKaehler
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_formallyEtale_aeval_of_isUnit_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
section
private theorem formallyEtale_away_of_isUnit_det (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (g : S) (T : Type*) [CommRing T] [Algebra S T] [IsLocalization (Submonoid.powers g) T]
    (w : ι → S)
    (hdet : IsUnit (algebraMap S T
      ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (w i)))) :
    @Algebra.FormallyEtale (MvPolynomial ι k) T _ _
      (RingHom.toAlgebra
        (MvPolynomial.eval₂Hom ((algebraMap S T).comp (algebraMap k S))
          (fun j : ι => algebraMap S T (w j)))) := by
  classical
  let instKT : Algebra k T := ((algebraMap S T).comp (algebraMap k S)).toAlgebra
  let instAlgebraMvPolynomial : Algebra (MvPolynomial ι k) T :=
    ((algebraMap S T).comp (algebraMap (MvPolynomial ι k) S)).toAlgebra
  have instTkS : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTPS : IsScalarTower (MvPolynomial ι k) S T :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTkP : IsScalarTower k (MvPolynomial ι k) T :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k S T x,
        IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S x]
      rfl
  have instFEST : Algebra.FormallyEtale S T :=
    Algebra.FormallyEtale.of_isLocalization (M := Submonoid.powers g)
  have instFEPT : Algebra.FormallyEtale (MvPolynomial ι k) T :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) S T
  have instFSkT : Algebra.FormallySmooth k T :=
    Algebra.FormallySmooth.comp k (MvPolynomial ι k) T
  have hdet' : IsUnit ((basisKaehler k ι T).det
      fun i : ι => KaehlerDifferential.D k T (algebraMap S T (w i))) := by
    rw [← algebraMap_det_basisKaehler k ι S T w]
    exact hdet
  have h := formallyEtale_aeval_of_isUnit_det (basisKaehler k ι T)
    (fun i : ι => algebraMap S T (w i)) hdet'
  exact h
end
section
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  [IsNoetherianRing S] (I q : Ideal S) [q.IsPrime]
end
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  [IsNoetherianRing S] (I q : Ideal S) [q.IsPrime]
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution
    (A : Type*) [CommRing A] [Algebra S A] [Algebra k A] [IsScalarTower k S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra.FormallySmooth k (A ⧸ Ideal.map (algebraMap S A) I)]
    (hIq : I ≤ q) :
    ∃ (g : S) (w : ι → S) (T : Finset ι),
      g ∉ q ∧
      (∀ j ∈ T, w j ∈ I) ∧
      Ideal.map (algebraMap S (Localization.Away g)) (Ideal.span (w '' (↑T : Set ι))) =
        Ideal.map (algebraMap S (Localization.Away g)) I ∧
      (∀ j ∉ T, ∃ i : ι, w j = coord k ι S i) ∧
      @Algebra.FormallyEtale (MvPolynomial ι k) (Localization.Away g) _ _
        (RingHom.toAlgebra
          (MvPolynomial.eval₂Hom
            ((algebraMap S (Localization.Away g)).comp (algebraMap k S))
            (fun j : ι => algebraMap S (Localization.Away g) (w j)))) := by
  classical
  obtain ⟨g, w, T, hgq, hwI, hmap, hcoord, hdet⟩ :=
    exists_away_ideal_eq_span_and_isUnit_det k ι S I q A hIq
  exact ⟨g, w, T, hgq, hwI, hmap, hcoord,
    formallyEtale_away_of_isUnit_det k ι S g (Localization.Away g) w hdet⟩
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
