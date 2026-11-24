-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.detProductRest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:26.848531+00:00
-- url     : https://prove2.me/submissions/5582fa6a-3e4e-41db-800c-977f4aa2c12c

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_AlternatingBinomial
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MinimumChainBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.LatticeBaseChangeAlt
open Real
private theorem pow_sub_pow_le_mul_sub_mul_pow {x y M : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hxM : x ≤ M) (hM : 1 ≤ M) :
    ∀ n : ℕ, x ^ n - y ^ n ≤ n * (x - y) * M ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : 0 ≤ x := hy.trans hyx
    have hxy : 0 ≤ x - y := sub_nonneg.2 hyx
    have hMn : 0 ≤ M ^ n := pow_nonneg (by linarith) n
    have hyn : y ^ n ≤ M ^ n := by
      first
      | exact pow_le_pow_left hy (hyx.trans hxM) n
      | exact pow_le_pow_left₀ hy (hyx.trans hxM) n
      | (gcongr <;> linarith)
    have hMn1 : M ^ n ≤ M ^ (n + 1) := by
      rw [pow_succ]; nlinarith [mul_nonneg hMn (sub_nonneg.2 hM)]
    have h1 : x * (x ^ n - y ^ n) ≤ x * (n * (x - y) * M ^ n) := mul_le_mul_of_nonneg_left ih hx
    have h2 : x * (n * (x - y) * M ^ n) ≤ M * (n * (x - y) * M ^ n) :=
      mul_le_mul_of_nonneg_right hxM (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hxy) hMn)
    have h3 : (x - y) * y ^ n ≤ (x - y) * M ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (hyn.trans hMn1) hxy
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    have e2 : M * (n * (x - y) * M ^ n) = n * (x - y) * M ^ (n + 1) := by ring
    rw [e]
    push_cast
    linarith
end Formalism.LatticeBaseChangeAlt
end

set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
open Real
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : DetProductRest := by
  intro i c ε hε hε1
  have h2 : (0 : ℝ) ≤ 2 ^ c := by positivity
  have hM : (1 : ℝ) ≤ 2 ^ c + 1 := by linarith
  have key := pow_sub_pow_le_mul_sub_mul_pow h2 (by linarith : (2 : ℝ) ^ c ≤ 2 ^ c + ε)
    (by linarith : (2 : ℝ) ^ c + ε ≤ 2 ^ c + 1) hM i
  have e : (2 : ℝ) ^ c + ε - 2 ^ c = ε := by ring
  rw [e] at key
  rw [pow_mul]
  exact key
end Formalism.LatticeBaseChangeAlt
