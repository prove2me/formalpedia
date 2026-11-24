-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_derivIdealIterate_of_isUnit_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:09:38.161145+00:00
-- url     : https://prove2.me/submissions/5451aa14-c717-42b2-98c8-221a48d2a522

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_derivIdeal_of_isUnit_natCast
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_zero


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
theorem _root_.solution (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R)
    (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {I : Ideal R} {r : ℕ} (hI : idealOrder I = (r : ℕ∞)) {j : ℕ} (hj : j ≤ r) :
    idealOrder (derivIdealIterate k j I) = ((r - j : ℕ) : ℕ∞) := by
  revert hj
  induction j with
  | zero =>
      intro _
      rw [derivIdealIterate_zero, Nat.sub_zero]
      exact hI
  | succ j ih =>
      intro hj
      have hj' : j ≤ r := by omega
      have hprev := ih hj'
      have h1 : 1 ≤ r - j := by omega
      have h := idealOrder_derivIdeal_of_isUnit_natCast k x D hD hx hunit h1 hprev
      rw [derivIdealIterate_succ]
      have heq : r - j - 1 = r - (j + 1) := by omega
      rwa [heq] at h
end FunctorialResolution.EmbeddedResolution
