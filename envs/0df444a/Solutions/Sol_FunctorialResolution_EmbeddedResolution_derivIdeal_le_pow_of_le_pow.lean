-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_le_pow_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:00:18.120838+00:00
-- url     : https://prove2.me/submissions/39abbc2a-2374-4ca0-b292-1a948c7a97cd

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_pow_succ_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    {I P : Ideal S} {n : ℕ} (h : I ≤ P ^ n) : derivIdeal k I ≤ P ^ (n - 1) := by
  cases n with
  | zero =>
      have hP : P ^ (0 - 1) = (⊤ : Ideal S) := by
        rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
      exact le_of_le_of_eq le_top hP.symm
  | succ m =>
      have h2 : derivIdeal k I ≤ P ^ m :=
        (derivIdeal_mono k h).trans (derivIdeal_pow_succ_le_pow k P m)
      have hm : m + 1 - 1 = m := by omega
      exact le_of_le_of_eq h2 (congrArg (fun i => P ^ i) hm.symm)
end FunctorialResolution.EmbeddedResolution
