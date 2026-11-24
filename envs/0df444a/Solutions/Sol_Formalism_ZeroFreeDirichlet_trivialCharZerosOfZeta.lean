-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.trivialCharZerosOfZeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:28.511879+00:00
-- url     : https://prove2.me/submissions/92e0ae18-1146-444b-9c18-7764ab39bd33

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivReal
import Theorems.Thm_Formalism_ZeroFreeDirichlet_one_sub_prime_cpow_neg_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : TrivZeros := by
  intro q _ s hs hs1 h0
  have hmul := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs1
  have h0' : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s = 0 := by
    rw [← hmul]
    exact h0
  rcases mul_eq_zero.1 h0' with h | h
  · exfalso
    obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.1 h
    exact one_sub_prime_cpow_neg_ne_zero p (Nat.prime_of_mem_primeFactors hp) hs hp0
  · exact h
end Formalism.ZeroFreeDirichlet
