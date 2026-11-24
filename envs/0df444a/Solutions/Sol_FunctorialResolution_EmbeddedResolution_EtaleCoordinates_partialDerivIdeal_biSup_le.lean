-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.partialDerivIdeal_biSup_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:46.010843+00:00
-- url     : https://prove2.me/submissions/85b1110d-d15f-44ff-b9c0-8ee7dc9a685b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativesInBlowupCharts
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_ControlledTransformLogDerivativesInCharts
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdeal_iSup_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*)
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (h : ι) (n : ℕ) (F : ℕ → Ideal S) :
    partialDerivIdeal k ι S h (⨆ i, ⨆ _ : i ≤ n, F i) ≤
      ⨆ i, ⨆ _ : i ≤ n, partialDerivIdeal k ι S h (F i) :=
  (partialDerivIdeal_iSup_le k ι S h (fun i => ⨆ _ : i ≤ n, F i)).trans
    (iSup_mono fun i => partialDerivIdeal_iSup_le k ι S h (fun _ : i ≤ n => F i))
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
