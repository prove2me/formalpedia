-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.harmonicCoeff_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:35.633907+00:00
-- url     : https://prove2.me/submissions/b35b8f89-7d25-45c6-960f-e5a0235e8a7f

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harmonic_identity_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution [CharZero K] {M N : ℕ} (h : N < M) :
    cP K M N + cP K M (N + 1) * (((N + 1) * (M - N) : ℕ) : K) = 0 := by
  unfold cP
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
  exact harmonic_identity_cancel _ _ _ _ _ _ (Nat.cast_ne_zero.2 (Nat.choose_pos h.le).ne')
    (Nat.cast_ne_zero.2 (Nat.choose_pos h).ne') (Nat.cast_ne_zero.2 (Nat.succ_ne_zero N))
    (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero N))
    (by rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_succ_right_eq])
end Formalism.CountingSumsFrames.Har2
