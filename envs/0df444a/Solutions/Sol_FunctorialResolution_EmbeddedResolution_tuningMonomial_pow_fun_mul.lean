-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningMonomial_pow_fun_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:23.820285+00:00
-- url     : https://prove2.me/submissions/d50056ad-fac4-4fad-9371-b4e0062d5032

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_eq_prod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
section
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
private theorem prod_derivIdealIterate_pow_pow (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    (∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j) ^ n
      = ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ (n * c j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, mul_pow, ih, Finset.prod_range_succ, ← pow_mul,
        Nat.mul_comm (c m) n]
section
variable [Algebra ℚ S]
end
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (fun j => n * c j) := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod]
  exact prod_derivIdealIterate_pow_pow k J m n c
end FunctorialResolution.EmbeddedResolution
