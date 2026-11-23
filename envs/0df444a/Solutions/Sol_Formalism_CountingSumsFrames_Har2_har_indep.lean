-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.har_indep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:44.26716+00:00
-- url     : https://prove2.me/submissions/ca9d9d98-9cfc-40e4-b945-c91c30f4b3b8

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_pow_h_pow_har

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
theorem _root_.solution [CharZero K] (hk : 1 ≤ k) (n : ℕ) : ∀ (a b : ℕ → ℕ) (w : ℕ → PolXY K k),
    (∀ j, w j ∈ HarAB K k (a j) (b j)) → ∑ j ∈ range n, hXY K k ^ j * w j = 0 → ∀ j < n, w j = 0 := by
  induction n with
  | zero => intro a b w _ _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    intro a b w hw hs
    have hwn : w n = 0 := by
      have h1 : (ctrF K k ^ n) (∑ j ∈ range (n + 1), hXY K k ^ j * w j) = 0 := by rw [hs, map_zero]
      have hz : ∑ j ∈ range n, (ctrF K k ^ n) (hXY K k ^ j * w j) = 0 :=
        Finset.sum_eq_zero fun j hj => by
          rw [ctr_pow_h_pow_har hk (hw j) n j,
            Nat.descFactorial_eq_zero_iff_lt.2 (Finset.mem_range.1 hj), zero_mul, Nat.cast_zero, zero_smul]
      rw [map_sum, Finset.sum_range_succ, hz, zero_add, ctr_pow_h_pow_har hk (hw n) n n, Nat.sub_self,
        pow_zero, one_mul, smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exfalso
        rw [Nat.cast_eq_zero, mul_eq_zero, Nat.descFactorial_self, Nat.descFactorial_eq_zero_iff_lt] at h1
        rcases h1 with h1 | h1
        · exact Nat.factorial_ne_zero n h1
        · omega
      · exact h1
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [Finset.sum_range_succ, hwn, mul_zero, add_zero] at hs
      exact ih a b w hw hs j hj
    · rw [hj]; exact hwn
end Formalism.CountingSumsFrames.Har2
