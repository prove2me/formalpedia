-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_isClosed_singleton_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:42.266039+00:00
-- url     : https://prove2.me/submissions/6655f3b7-d2f9-4fd2-b5da-34e9b04a461c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_AffineSpaceJacobson
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StalkKrullDimension
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
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_isClosed_singleton_of_isAffine (A : Scheme.{u}) [IsAffine A] (a : A) :
    ∃ x : A, IsClosed ({x} : Set A) := by
  have h : ↥A ≃ₜ PrimeSpectrum ↥Γ(A, ⊤) := Scheme.homeoOfIso A.isoSpec
  have hp : PrimeSpectrum ↥Γ(A, ⊤) := h a
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal hp.asIdeal hp.isPrime.ne_top
  refine ⟨h.symm ⟨M, hM.isPrime⟩, ?_⟩
  have hq : IsClosed ({(⟨M, hM.isPrime⟩ : PrimeSpectrum ↥Γ(A, ⊤))} :
      Set (PrimeSpectrum ↥Γ(A, ⊤))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hM
  have h2 := h.symm.isClosedMap _ hq
  rwa [Set.image_singleton] at h2
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ x : U.toScheme, IsClosed ({x} : Set U.toScheme) := by
  have : IsAffine U.toScheme := hU
  obtain ⟨x0, hx0⟩ := hne
  exact exists_isClosed_singleton_of_isAffine U.toScheme ⟨x0, hx0⟩
end FunctorialResolution.EmbeddedResolution
