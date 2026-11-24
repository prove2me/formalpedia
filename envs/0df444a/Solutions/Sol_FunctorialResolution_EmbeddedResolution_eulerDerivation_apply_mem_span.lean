-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.eulerDerivation_apply_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:37.533806+00:00
-- url     : https://prove2.me/submissions/aa74bdb2-8d5e-4e36-aaba-a90bc5968d5d

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
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    eulerDerivation k x D a ∈ Ideal.span (Set.range x) := by
  rw [eulerDerivation_apply]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
end FunctorialResolution.EmbeddedResolution
