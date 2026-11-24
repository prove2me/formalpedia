-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_le_idealOrder_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:27.861675+00:00
-- url     : https://prove2.me/submissions/c8e0b63a-3ea5-452e-b066-b13f60624693

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
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
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
private theorem map_maximalIdeal_pow_le_pow (f : R →+* S)
    (hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S) (n : ℕ) :
    ((IsLocalRing.maximalIdeal R) ^ n).map f ≤ (IsLocalRing.maximalIdeal S) ^ n := by
  induction n with
  | zero =>
      have hS : (IsLocalRing.maximalIdeal S) ^ 0 = (⊤ : Ideal S) := by
        rw [pow_zero, Ideal.one_eq_top]
      rw [hS]
      exact le_top
  | succ n ih =>
      rw [pow_succ, pow_succ, Ideal.map_mul]
      exact Ideal.mul_mono ih hf
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (f : R →+* S)
    (hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S) (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map f) := by
  refine ENat.forall_natCast_le_iff_le.mp (fun n hn => ?_)
  rw [le_idealOrder_iff] at hn ⊢
  exact le_trans (Ideal.map_mono hn) (map_maximalIdeal_pow_le_pow f hf n)
end FunctorialResolution.EmbeddedResolution
