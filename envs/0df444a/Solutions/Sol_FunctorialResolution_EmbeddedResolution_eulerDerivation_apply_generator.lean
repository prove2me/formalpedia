-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.eulerDerivation_apply_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:36.459401+00:00
-- url     : https://prove2.me/submissions/66f7d546-faf8-4b9c-9227-b9559c3c59a2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_eulerDerivation_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (j : ι) :
    eulerDerivation k x D (x j) = x j := by
  rw [eulerDerivation_apply]
  simp [hD]
end FunctorialResolution.EmbeddedResolution
