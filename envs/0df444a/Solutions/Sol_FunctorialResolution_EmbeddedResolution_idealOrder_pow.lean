-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:14:07.179803+00:00
-- url     : https://prove2.me/submissions/d2425f16-20c1-4ee9-ae3c-b6482ce4a661

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LeadingForm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply



set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k R : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] {h : ℕ} (x : Fin h → R) (D : Fin h → Derivation k R R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hDD : ∀ i j : Fin h, ∀ a : R, D i (D j a) = D j (D i a))
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R)) (I : Ideal R) (c : ℕ) :
    idealOrder (I ^ c) = (c : ℕ∞) * idealOrder I := by
  induction c with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, idealOrder_top]
    simp
  | succ c ih =>
    rw [pow_succ, idealOrder_mul x D hx hD hDD hunit, ih, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]
end FunctorialResolution.EmbeddedResolution
