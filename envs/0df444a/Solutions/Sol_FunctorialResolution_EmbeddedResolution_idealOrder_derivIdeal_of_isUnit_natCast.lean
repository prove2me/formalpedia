-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_derivIdeal_of_isUnit_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:54:05.521989+00:00
-- url     : https://prove2.me/submissions/bb514366-0b03-49d4-b95f-70a72315312d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_not_derivIdeal_le_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_pow_of_le_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_idealOrder_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open IsLocalRing
private theorem eq_natCast_of_le_of_not_succ_le (n : ℕ) (a : ℕ∞) (h1 : (n : ℕ∞) ≤ a)
    (h2 : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ a) : a = (n : ℕ∞) := by
  rcases eq_top_or_lt_top a with rfl | hlt
  · exact absurd le_top h2
  · lift a to ℕ using hlt.ne
    have hn : n ≤ a := by exact_mod_cast h1
    have hn2 : ¬ (n + 1 ≤ a) := by
      intro hc
      exact h2 (by exact_mod_cast hc)
    have ha : a = n := by omega
    exact_mod_cast ha
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {I : Ideal R} {r : ℕ} (hr : 1 ≤ r) (hI : idealOrder I = (r : ℕ∞)) :
    idealOrder (derivIdeal k I) = ((r - 1 : ℕ) : ℕ∞) := by
  have hIr : I ≤ IsLocalRing.maximalIdeal R ^ r := (le_idealOrder_iff I r).mp hI.ge
  have hIr1 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (r + 1) := by
    intro hc
    have h := (le_idealOrder_iff I (r + 1)).mpr hc
    rw [hI] at h
    have h' : r + 1 ≤ r := by exact_mod_cast h
    omega
  have hunitr : IsUnit ((r : ℕ) : R) := hunit r hr
  have hnot : ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r :=
    not_derivIdeal_le_pow k x D hD hunitr (by rw [hx]; exact hIr) (by rw [hx]; exact hIr1)
  have hle : derivIdeal k I ≤ IsLocalRing.maximalIdeal R ^ (r - 1) :=
    derivIdeal_le_pow_of_le_pow k hIr
  have h1 : ((r - 1 : ℕ) : ℕ∞) ≤ idealOrder (derivIdeal k I) :=
    (le_idealOrder_iff _ (r - 1)).mpr hle
  have h2 : ¬ (((r - 1) + 1 : ℕ) : ℕ∞) ≤ idealOrder (derivIdeal k I) := by
    intro hc
    have h := (le_idealOrder_iff _ ((r - 1) + 1)).mp hc
    apply hnot
    rw [hx]
    have hrr : (r - 1) + 1 = r := by omega
    rwa [hrr] at h
  exact eq_natCast_of_le_of_not_succ_le (r - 1) _ h1 h2
end FunctorialResolution.EmbeddedResolution
