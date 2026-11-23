-- Prove2me | solution 1 for Formalism.CountingSumsFrames.clog_le_logb_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:18.716082+00:00
-- url     : https://prove2.me/submissions/d6b71a12-e6e4-43ee-9007-9ba00c6a1dc8

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished

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
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (p n : ℕ) (x : ℝ) (hp : 2 ≤ p) (hx : 1 ≤ x) (hn : (n : ℝ) ≤ x) :
    (Nat.clog p n : ℝ) ≤ Real.logb p x + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  rcases Nat.lt_or_ge 1 n with h | h
  · have hlt : p ^ (Nat.clog p n).pred < n := Nat.pow_pred_clog_lt_self (by omega) h
    have hlt' : (p : ℝ) ^ (Nat.clog p n).pred ≤ x := by
      have : ((p ^ (Nat.clog p n).pred : ℕ) : ℝ) < n := by exact_mod_cast hlt
      push_cast at this; linarith
    have h1 : (((Nat.clog p n).pred : ℕ) : ℝ) = Real.logb p ((p : ℝ) ^ (Nat.clog p n).pred) := by
      rw [Real.logb_pow, Real.logb_self_eq_one hp1]; ring
    have h2 : Real.logb p ((p : ℝ) ^ (Nat.clog p n).pred) ≤ Real.logb p x :=
      Real.logb_le_logb_of_le hp1 (by positivity) hlt'
    have h3 : Nat.clog p n ≤ (Nat.clog p n).pred + 1 := by
      simp only [Nat.pred_eq_sub_one]; omega
    have h3' : (Nat.clog p n : ℝ) ≤ ((Nat.clog p n).pred : ℕ) + 1 := by exact_mod_cast h3
    linarith
  · rw [Nat.clog_of_right_le_one h]
    have := Real.logb_nonneg hp1 hx
    simp; linarith
end Formalism.CountingSumsFrames
