-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdeal_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:19.992739+00:00
-- url     : https://prove2.me/submissions/9b84fb5f-328c-440b-af62-1fc95da49fa6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]
private theorem partialDerivIdeal_def (h : ι) (J : Ideal S) :
    partialDerivIdeal k ι S h J =
      J ⊔ Ideal.span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x} := rfl
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (h : ι) (J K : Ideal S) :
    partialDerivIdeal k ι S h J ≤ K ↔ J ≤ K ∧ ∀ g ∈ J, partialDeriv k ι S h g ∈ K := by
  rw [partialDerivIdeal_def, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g hg => h2 ⟨g, hg, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact h2 g hg
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
