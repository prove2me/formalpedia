-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.not_derivIdeal_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:38:16.473806+00:00
-- url     : https://prove2.me/submissions/4d074884-273e-4536-9e26-b358a137d216

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_pow_succ_of_deriv_mem_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_derivIdeal


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
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
    {I : Ideal R} (h1 : I ≤ Ideal.span (Set.range x) ^ r)
    (h2 : ¬ I ≤ Ideal.span (Set.range x) ^ (r + 1)) :
    ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r := by
  intro h
  apply h2
  intro f hf
  exact mem_pow_succ_of_deriv_mem_pow k x D hD hr (h1 hf)
    (fun i => h (derivation_apply_mem_derivIdeal k I (D i) hf))
end FunctorialResolution.EmbeddedResolution
