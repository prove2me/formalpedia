-- Prove2me | solution 1 for FinancialDerivatives.FD04.chooserInitial_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:00:51.394814+00:00
-- url     : https://prove2.me/submissions/a1b15808-87f4-4c0b-aa30-fd2e71587cb4

import Mathlib.Tactic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd03_constantPayoffTree
import Definitions.Def_fd04_chooserInitialValue
import Definitions.Def_fd04_callInitialValue
import Definitions.Def_fd04_putInitialValue
import Definitions.Def_fd04_compoundCallInitialValue
import Definitions.Def_fd04_knockOutCallPayoff
import Definitions.Def_fd04_knockInCallPayoff
import Definitions.Def_fd04_discountedStrike
import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_callAtChoice

namespace S84FD
open FinancialDerivatives.FD03 FinancialDerivatives.FD04

theorem gpos (m : BinomialMarket) : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
theorem w0 (m : BinomialMarket) : 0 < upWeight m := by
  unfold upWeight
  exact div_pos (by linarith [m.down_lt_growth]) (by linarith [m.down_lt_growth, m.growth_lt_up])
theorem w1 (m : BinomialMarket) : upWeight m < 1 := by
  unfold upWeight
  rw [div_lt_one (by linarith [m.down_lt_growth, m.growth_lt_up])]
  linarith [m.growth_lt_up]

theorem ev_add (m : BinomialMarket) (n : ℕ) (t : PayoffTree n) (f g : ℝ → ℝ) :
    europeanValue m n (payoffTreeMap (fun x => f x + g x) n t) =
      europeanValue m n (payoffTreeMap f n t) + europeanValue m n (payoffTreeMap g n t) := by
  induction n with
  | zero => cases t; rfl
  | succ n ih =>
    cases t with
    | branch up down =>
      simp only [payoffTreeMap, europeanValue, ih]
      unfold oneStepValue; ring

theorem ev_smul (m : BinomialMarket) (n : ℕ) (t : PayoffTree n) (c : ℝ) (f : ℝ → ℝ) :
    europeanValue m n (payoffTreeMap (fun x => c * f x) n t) =
      c * europeanValue m n (payoffTreeMap f n t) := by
  induction n with
  | zero => cases t; rfl
  | succ n ih =>
    cases t with
    | branch up down =>
      simp only [payoffTreeMap, europeanValue, ih]
      unfold oneStepValue; ring

theorem ev_const (m : BinomialMarket) (n : ℕ) (t : PayoffTree n) (c : ℝ) :
    europeanValue m n (payoffTreeMap (fun _ => c) n t) = c / m.growth ^ n := by
  induction n with
  | zero => cases t; simp [payoffTreeMap, europeanValue]
  | succ n ih =>
    cases t with
    | branch up down =>
      simp only [payoffTreeMap, europeanValue, ih]
      have := (gpos m).ne'
      unfold oneStepValue; rw [pow_succ]; field_simp; ring

theorem ev_mono (m : BinomialMarket) (n : ℕ) (t : PayoffTree n) (f g : ℝ → ℝ)
    (h : ∀ x, f x ≤ g x) :
    europeanValue m n (payoffTreeMap f n t) ≤ europeanValue m n (payoffTreeMap g n t) := by
  induction n with
  | zero => cases t; exact h _
  | succ n ih =>
    cases t with
    | branch up down =>
      simp only [payoffTreeMap, europeanValue]
      unfold oneStepValue
      have h1 := ih up; have h2 := ih down
      have := w0 m; have := w1 m
      apply div_le_div_of_nonneg_right _ (gpos m).le
      nlinarith

theorem ev_nonneg (m : BinomialMarket) (n : ℕ) (t : PayoffTree n) (f : ℝ → ℝ)
    (h : ∀ x, 0 ≤ f x) : 0 ≤ europeanValue m n (payoffTreeMap f n t) := by
  have := ev_mono m n t (fun _ => 0) f h
  rw [ev_const, zero_div] at this; exact this

theorem map_id (n : ℕ) (t : PayoffTree n) : payoffTreeMap (fun x => x) n t = t := by
  induction n with
  | zero => cases t; rfl
  | succ n ih => cases t; simp only [payoffTreeMap, ih]

theorem ev_stock (m : BinomialMarket) (n : ℕ) (spot : ℝ) :
    europeanValue m n (terminalStockTree m n spot) = spot := by
  induction n generalizing spot with
  | zero => rfl
  | succ n ih =>
    simp only [terminalStockTree, europeanValue, ih]
    have h1 : m.up - m.down ≠ 0 := by linarith [m.down_lt_growth, m.growth_lt_up]
    have h2 : m.growth ≠ 0 := by linarith [m.down_pos, m.down_lt_growth]
    unfold oneStepValue upWeight
    field_simp
    ring

theorem tower (m : BinomialMarket) (f : ℝ → ℝ) (b a : ℕ) (spot : ℝ) :
    europeanValue m a (payoffTreeMap
      (fun s => europeanValue m b (payoffTreeMap f b (terminalStockTree m b s))) a
      (terminalStockTree m a spot)) =
    europeanValue m (b + a) (payoffTreeMap f (b + a) (terminalStockTree m (b + a) spot)) := by
  induction a generalizing spot with
  | zero => rfl
  | succ a ih =>
    simp only [terminalStockTree, payoffTreeMap, europeanValue, ih]
    rfl

theorem call_sub_put (m : BinomialMarket) (K spot : ℝ) (n : ℕ) :
    callAtChoice m K n spot - putAtChoice m K n spot = spot - discountedStrike m K n := by
  unfold callAtChoice putAtChoice discountedStrike
  have e : callPayoff K = fun x => (x + (-1) * K) + 1 * putPayoff K x := by
    funext x; unfold callPayoff putPayoff
    rcases le_total x K with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [e, ev_add, ev_add, ev_smul, ev_smul, map_id, ev_stock, ev_const]
  ring

end S84FD


namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

open S84FD in
theorem _root_.solution (m : BinomialMarket)
    (K : ℝ) (choiceSteps postChoiceSteps : ℕ) :
    chooserInitialValue m K choiceSteps postChoiceSteps =
      europeanValue m choiceSteps
        (payoffTreeMap (callAtChoice m K postChoiceSteps) choiceSteps
          (terminalStockTree m choiceSteps m.initialSpot)) +
      putInitialValue m (discountedStrike m K postChoiceSteps)
        choiceSteps := by
  unfold chooserInitialValue putInitialValue putAtChoice
  have : chooserAtChoice m K postChoiceSteps = fun s => callAtChoice m K postChoiceSteps s + putPayoff (discountedStrike m K postChoiceSteps) s := by
    funext spot
    have h := call_sub_put m K spot postChoiceSteps
    unfold chooserAtChoice putPayoff
    rcases le_total (callAtChoice m K postChoiceSteps spot) (putAtChoice m K postChoiceSteps spot) with h1 | h1
    · rw [max_eq_right h1, max_eq_left (by linarith)]; linarith
    · rw [max_eq_left h1, max_eq_right (by linarith)]; ring
  rw [this, ev_add]

end FinancialDerivatives.FD04
