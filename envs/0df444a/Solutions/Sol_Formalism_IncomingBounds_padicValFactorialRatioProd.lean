-- Prove2me | solution 1 for Formalism.IncomingBounds.padicValFactorialRatioProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:18.608466+00:00
-- url     : https://prove2.me/submissions/9a906117-8cbc-4391-b3a4-6c62c576ab6b

import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
private theorem sub_one_mul_padicValNat_factorial_eq (l m : ℕ) (hl : l.Prime) :
    ((l : ℝ) - 1) * (padicValNat l m.factorial : ℝ) = (m : ℝ) - ((l.digits m).sum : ℝ) := by
  have := Fact.mk hl
  have h := sub_one_mul_padicValNat_factorial (p := l) m
  have hs := Nat.digit_sum_le l m
  have h1 : 1 ≤ l := hl.one_lt.le
  have h' : (((l - 1) * padicValNat l m.factorial : ℕ) : ℝ) = ((m - (l.digits m).sum : ℕ) : ℝ) := by
    rw [h]
  push_cast [Nat.cast_sub h1, Nat.cast_sub hs] at h'
  simpa [Nat.cast_list_sum] using h'
private theorem digits_sum_le_sub_one_mul_logb_add_one (l a : ℕ) (hl : 2 ≤ l) (n : ℕ) (ha : a < n) :
    ((l.digits a).sum : ℝ) ≤ ((l : ℝ) - 1) * (Real.logb l n + 1) := by
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog0 : 0 ≤ Real.logb l n := Real.logb_nonneg (by linarith) hn
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0
    simp only [Nat.digits_zero, List.sum_nil, Nat.cast_zero]
    exact mul_nonneg (by linarith) (by linarith)
  · have hlen : (l.digits a).length = Nat.log l a + 1 := Nat.digits_len l a (by omega) (by omega)
    have hsum : (l.digits a).sum ≤ (l.digits a).length • (l - 1) :=
      List.sum_le_card_nsmul (l.digits a) (l - 1) (fun x hx => by
        have := Nat.digits_lt_base (by omega) hx
        omega)
    rw [hlen, smul_eq_mul] at hsum
    have hsumR : ((l.digits a).sum : ℝ) ≤ ((Nat.log l a : ℝ) + 1) * ((l : ℝ) - 1) := by
      have h' : (((l.digits a).sum : ℕ) : ℝ) ≤ (((Nat.log l a + 1) * (l - 1) : ℕ) : ℝ) := by
        exact_mod_cast hsum
      push_cast [Nat.cast_sub (show 1 ≤ l by omega)] at h'
      simpa [Nat.cast_list_sum] using h'
    have hlog : (Nat.log l a : ℝ) ≤ Real.logb l n := by
      have hpow : l ^ Nat.log l a ≤ a := Nat.pow_log_le_self l (by omega)
      rw [Real.le_logb_iff_rpow_le (by linarith) (by linarith), Real.rpow_natCast]
      exact_mod_cast hpow.trans ha.le
    nlinarith [mul_le_mul_of_nonneg_right hlog (by linarith : (0:ℝ) ≤ (l : ℝ) - 1)]
private theorem padicValNat_factorial_div_factorial_le (l : ℕ) (hl : l.Prime) (y a n : ℕ) (ha : a < n) :
    (padicValNat l ((y + a).factorial / a.factorial) : ℝ) ≤
      (y : ℝ) / ((l : ℝ) - 1) + (Real.logb l n + 1) := by
  have := Fact.mk hl
  have hdvd : a.factorial ∣ (y + a).factorial := Nat.factorial_dvd_factorial (by omega)
  have hq0 : (y + a).factorial / a.factorial ≠ 0 :=
    (Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos a)).ne'
  have hsplit : (y + a).factorial = a.factorial * ((y + a).factorial / a.factorial) :=
    (Nat.mul_div_cancel' hdvd).symm
  have hv : padicValNat l (y + a).factorial =
      padicValNat l a.factorial + padicValNat l ((y + a).factorial / a.factorial) := by
    rw [← padicValNat.mul (Nat.factorial_ne_zero a) hq0, ← hsplit]
  have hv' : (padicValNat l (y + a).factorial : ℝ) =
      (padicValNat l a.factorial : ℝ) + (padicValNat l ((y + a).factorial / a.factorial) : ℝ) := by
    exact_mod_cast hv
  have e1 := sub_one_mul_padicValNat_factorial_eq l (y + a) hl
  have e2 := sub_one_mul_padicValNat_factorial_eq l a hl
  rw [hv', Nat.cast_add] at e1
  have hs := digits_sum_le_sub_one_mul_logb_add_one l a hl.two_le n ha
  have hs0 : (0 : ℝ) ≤ ((l.digits (y + a)).sum : ℝ) := Nat.cast_nonneg _
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hlpos : 0 < (l : ℝ) - 1 := by linarith
  have key : ((l : ℝ) - 1) * (padicValNat l ((y + a).factorial / a.factorial) : ℝ) ≤
      (y : ℝ) + ((l : ℝ) - 1) * (Real.logb l n + 1) := by
    nlinarith
  rw [div_add' _ _ _ hlpos.ne', le_div_iff₀ hlpos]
  nlinarith
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : CapVal := by
  intro l hl n0 n y hn0
  have := Fact.mk hl
  have hprod : ∀ m, m ≤ n → (padicValNat l (capNat m y) : ℝ) ≤
      (m : ℝ) * y / ((l : ℝ) - 1) + m * (Real.logb l n + 1) := by
    intro m
    induction m with
    | zero => intro _; simp [capNat]
    | succ m ih =>
      intro hm
      have hne1 : capNat m y ≠ 0 := by
        unfold capNat
        rw [Finset.prod_ne_zero_iff]
        intro a _
        exact (Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos a)).ne'
      have hne2 : (y + m).factorial / m.factorial ≠ 0 :=
        (Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos m)).ne'
      have hsplit : capNat (m + 1) y =
          capNat m y * ((y + m).factorial / m.factorial) := by
        unfold capNat
        rw [Finset.prod_range_succ]
      rw [hsplit, padicValNat.mul hne1 hne2]
      push_cast
      have h1 := ih (by omega)
      have h2 := padicValNat_factorial_div_factorial_le l hl y m n (by omega)
      have e : ((m : ℝ) + 1) * y / ((l : ℝ) - 1) = (m : ℝ) * y / ((l : ℝ) - 1) + y / ((l : ℝ) - 1) := by
        ring
      linarith
  have h := hprod n0 hn0
  have hL : 0 ≤ Real.logb l n + 1 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h0
      have := Real.logb_nonneg (b := (l : ℝ)) (by exact_mod_cast hl.one_lt) h1
      linarith
  have hn0R : (n0 : ℝ) ≤ n := by exact_mod_cast hn0
  nlinarith [mul_le_mul_of_nonneg_right hn0R hL]
end Formalism.IncomingBounds
