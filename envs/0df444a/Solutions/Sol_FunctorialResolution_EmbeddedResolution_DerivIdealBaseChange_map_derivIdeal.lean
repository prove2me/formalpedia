-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange.map_derivIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:21:57.946813+00:00
-- url     : https://prove2.me/submissions/5bfb7244-2145-44c1-a491-77ac8cb187a2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealFieldExtension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_DerivIdealBaseChange_map_derivIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_DerivIdealBaseChange_derivIdeal_map_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (L : Type*) [CommRing L] [Algebra k L]
  (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S' : Type*) [CommRing S'] [Algebra L S'] [Algebra (MvPolynomial ι L) S']
  [IsScalarTower L (MvPolynomial ι L) S'] [Algebra.FormallyEtale (MvPolynomial ι L) S']
  [Algebra k S'] [IsScalarTower k L S']
namespace FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
theorem _root_.solution [Fintype ι] (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (J : Ideal S) :
    Ideal.map φ (derivIdeal k J) = derivIdeal L (Ideal.map φ J) :=
  le_antisymm
    (map_derivIdeal_le (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ J)
    (derivIdeal_map_le (k := k) (L := L) (ι := ι) (S := S) (S' := S') φ hφ J)
end FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
