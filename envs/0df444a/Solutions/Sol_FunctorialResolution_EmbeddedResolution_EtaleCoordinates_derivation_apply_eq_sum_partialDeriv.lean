-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.derivation_apply_eq_sum_partialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:01:23.209709+00:00
-- url     : https://prove2.me/submissions/b6db747f-9cfe-48b9-a440-c76929954c2f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_eq_sum_smul_partialDeriv

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
omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S] in
private theorem derivation_sum_apply (s : Finset ι) (f : ι → Derivation k S S) (g : S) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g :=
  map_sum (evalDerivationAddHom k S g) f s
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
theorem _root_.solution [Fintype ι] (D : Derivation k S S) (g : S) :
    D g = ∑ i, D (coord k ι S i) * partialDeriv k ι S i g := by
  have h1 : D g = (∑ i, D (coord k ι S i) • partialDeriv k ι S i : Derivation k S S) g :=
    congrArg (fun E : Derivation k S S => E g) (eq_sum_smul_partialDeriv k ι S D)
  have h2 : (∑ i, D (coord k ι S i) • partialDeriv k ι S i : Derivation k S S) g
      = ∑ i, D (coord k ι S i) * partialDeriv k ι S i g :=
    derivation_sum_apply k ι S Finset.univ (fun i => D (coord k ι S i) • partialDeriv k ι S i) g
  exact h1.trans h2
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
