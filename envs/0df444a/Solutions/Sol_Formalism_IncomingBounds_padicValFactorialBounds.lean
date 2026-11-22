-- Prove2me | solution 1 for Formalism.IncomingBounds.padicValFactorialBounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:56:58.79867+00:00
-- url     : https://prove2.me/submissions/56dbf2d7-17a6-436b-bada-1228538d2845

import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco

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
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : FactValBounds := by
  intro l hl N hN
  haveI := Fact.mk hl
  have key := sub_one_mul_padicValNat_factorial (p := l) N
  have hsN : (l.digits N).sum ≤ N := Nat.digit_sum_le l N
  have hne : l.digits N ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have hs1 : 1 ≤ (l.digits N).sum := by
    have hpos : 0 < (l.digits N).getLast hne :=
      Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero l (by omega))
    have := List.le_sum_of_mem (List.getLast_mem hne)
    omega
  have hdig : (l.digits N).sum ≤ (Nat.log l N + 1) * (l - 1) := by
    have hlen := Nat.digits_len l N hl.one_lt (by omega)
    have := List.sum_le_card_nsmul (l.digits N) (l - 1)
      (fun x hx => by have := Nat.digits_lt_base hl.one_lt hx; omega)
    rwa [smul_eq_mul, hlen] at this
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hl1 : (0 : ℝ) < l - 1 := by linarith
  have e := congrArg (fun t : ℕ => (t : ℝ)) key
  simp only [Nat.cast_mul, Nat.cast_sub hsN, Nat.cast_sub hl.one_le, Nat.cast_one] at e
  have hs1R : (1 : ℝ) ≤ ((l.digits N).sum : ℝ) := by exact_mod_cast hs1
  have hdigR := (Nat.cast_le (α := ℝ)).2 hdig
  simp only [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_add, Nat.cast_one] at hdigR
  have hlog : (Nat.log l N : ℝ) ≤ Real.logb l N := Real.natLog_le_logb N l
  constructor
  · have h : (N : ℝ) / ((l : ℝ) - 1) ≤ (padicValNat l N.factorial : ℝ) + ((Nat.log l N : ℝ) + 1) := by
      rw [div_le_iff₀ hl1]
      nlinarith
    linarith
  · rw [le_div_iff₀ hl1]
    nlinarith
end Formalism.IncomingBounds
