-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.span_pow_mul_tuningMonomial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:20:31.271858+00:00
-- url     : https://prove2.me/submissions/70d1c35d-119f-41e1-a3e4-55f7df83e64d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_add
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_nsmul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_single
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_single
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_le_tunedIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (n : ℕ) (c : ℕ → ℕ) :
    Ideal.span {x ^ n} * tuningMonomial k J m c ≤ tunedIdeal k J m (tuningWeight m c + n) := by
  have hmem : (m - 1) ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have hspan : Ideal.span {x ^ n} ≤ tuningMonomial k J m (n • Pi.single (m - 1) 1) := by
    rw [← tuningMonomial_pow, tuningMonomial_single k J m (m - 1) hmem,
      Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_mem_pow hx n
  refine le_trans (Ideal.mul_mono hspan le_rfl) ?_
  rw [tuningMonomial_mul]
  refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
  rw [tuningWeight_add, tuningWeight_nsmul, tuningWeight_single m (m - 1) hmem]
  have hmm : m - (m - 1) = 1 := by omega
  rw [hmm]
  omega
end FunctorialResolution.EmbeddedResolution
