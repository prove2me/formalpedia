-- Prove2me | solution 1 for CongestionPoA.AsymSum.theorem2_instance
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T17:44:51.664587+00:00
-- url     : https://prove2.me/submissions/1a152d3d-9d39-4993-b8b9-c2309b478c96

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model

/-!
# The cyclic lower-bound construction for every N ≥ 3

Christodoulou and Koutsoupias, *The Price of Anarchy of Finite Congestion Games*,
STOC 2005, Theorem 2 (published seven-page PDF p. 3; author eleven-page PDF p. 4).

Facilities are two copies of Fin N. Each player i may use {h_i, g_i} or
{g_(i+1), h_(i-1), h_(i+1)}, with cyclic arithmetic and identity latency.
The second choices form a Nash equilibrium of cost 5N. The first choices cost
2N and are optimal: each feasible strategy contains at least two facilities,
and every facility used by a player has load at least one.
-/

open Finset
open scoped BigOperators

namespace CongestionPoA.AsymSum.Theorem2Construction

open Fin.CommRing

variable {N : ℕ} [NeZero N]

/-- The first copy consists of the h facilities; the second consists of the g facilities. -/
abbrev Facility (N : ℕ) := Bool × Fin N

def good (i : Fin N) : Finset (Facility N) := {(false, i), (true, i)}

def bad (i : Fin N) : Finset (Facility N) :=
  {(true, i + 1), (false, i - 1), (false, i + 1)}

def game (N : ℕ) [NeZero N] : CongestionGame (Fin N) (Facility N) where
  strategies i := {good i, bad i}
  latency _ k := k

lemma one_ne_zero (hN : 3 ≤ N) : (1 : Fin N) ≠ 0 := by
  intro h
  have hv : (1 : ℕ) % N = (0 : ℕ) := congrArg Fin.val h
  rw [Nat.mod_eq_of_lt (show 1 < N by omega)] at hv
  contradiction

lemma two_ne_zero (hN : 3 ≤ N) : (2 : Fin N) ≠ 0 := by
  intro h
  have hv : (2 : ℕ) % N = (0 : ℕ) := congrArg Fin.val h
  rw [Nat.mod_eq_of_lt (show 2 < N by omega)] at hv
  contradiction

lemma next_ne_self (hN : 3 ≤ N) (i : Fin N) : i + 1 ≠ i := by
  intro h
  apply one_ne_zero hN
  exact add_left_cancel (show i + 1 = i + 0 by simpa using h)

lemma prev_ne_self (hN : 3 ≤ N) (i : Fin N) : i - 1 ≠ i := by
  intro h
  apply next_ne_self hN i
  simpa only [h] using (sub_add_cancel i (1 : Fin N))

lemma next_ne_prev (hN : 3 ≤ N) (i : Fin N) : i + 1 ≠ i - 1 := by
  intro h
  apply two_ne_zero hN
  linear_combination h

omit [NeZero N] in
lemma good_users (b : Bool) (j : Fin N) :
    (univ.filter fun i => (b, j) ∈ good i) = {j} := by
  ext i
  cases b <;> simp [good, eq_comm]

lemma bad_g_users (j : Fin N) :
    (univ.filter fun i => (true, j) ∈ bad i) = {j - 1} := by
  ext i
  simp [bad, eq_sub_iff_add_eq, eq_comm]

lemma bad_h_users (j : Fin N) :
    (univ.filter fun i => (false, j) ∈ bad i) = {j + 1, j - 1} := by
  ext i
  simp [bad, eq_sub_iff_add_eq, eq_comm]

omit [NeZero N] in
lemma load_good (b : Bool) (j : Fin N) : load good (b, j) = 1 := by
  rw [load, good_users]
  simp

lemma load_bad_g (j : Fin N) : load bad (true, j) = 1 := by
  rw [load, bad_g_users]
  simp

lemma load_bad_h (hN : 3 ≤ N) (j : Fin N) : load bad (false, j) = 2 := by
  rw [load, bad_h_users]
  simp [next_ne_prev hN j]

omit [NeZero N] in
lemma card_good (i : Fin N) : (good i).card = 2 := by
  simp [good]

lemma card_bad (hN : 3 ≤ N) (i : Fin N) : (bad i).card = 3 := by
  simp [bad, (next_ne_prev hN i).symm]

lemma cost_good (i : Fin N) : cost (game N) good i = 2 := by
  change (∑ e ∈ {(false, i), (true, i)}, (load good e : ℝ)) = 2
  norm_num [load_good]

lemma cost_bad (hN : 3 ≤ N) (i : Fin N) : cost (game N) bad i = 5 := by
  change (∑ e ∈ {(true, i + 1), (false, i - 1), (false, i + 1)},
    (load bad e : ℝ)) = 5
  norm_num [load_bad_g, load_bad_h hN, (next_ne_prev hN i).symm]

/-- Switching onto a previously unused facility increases its load by exactly one. -/
lemma load_update_new {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (Q : ι → Finset E) (i : ι) (e : E) (S : Finset E)
    (hQ : e ∉ Q i) (hS : e ∈ S) :
    load (Function.update Q i S) e = load Q e + 1 := by
  have hset : (univ.filter fun j => e ∈ Function.update Q i S j) =
      insert i (univ.filter fun j => e ∈ Q j) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [hS]
    · simp [hji]
  rw [load, hset, card_insert_of_notMem]
  · rfl
  · simpa using hQ

lemma good_disjoint_bad (hN : 3 ≤ N) (i : Fin N) (b : Bool) :
    (b, i) ∉ bad i := by
  cases b <;> simp [bad, (next_ne_self hN i).symm, (prev_ne_self hN i).symm]

lemma cost_deviation (hN : 3 ≤ N) (i : Fin N) :
    cost (game N) (Function.update bad i (good i)) i = 5 := by
  have hg : load (Function.update bad i (good i)) (true, i) = 2 := by
    rw [load_update_new bad i (true, i) (good i) (good_disjoint_bad hN i true)
      (by simp [good]), load_bad_g]
  have hh : load (Function.update bad i (good i)) (false, i) = 3 := by
    rw [load_update_new bad i (false, i) (good i) (good_disjoint_bad hN i false)
      (by simp [good]), load_bad_h hN]
  change (∑ e ∈ Function.update bad i (good i) i,
    (load (Function.update bad i (good i)) e : ℝ)) = 5
  simp only [Function.update_self]
  change (∑ e ∈ {(false, i), (true, i)},
    (load (Function.update bad i (good i)) e : ℝ)) = 5
  norm_num [hh, hg]

lemma isProfile_good : IsProfile (game N) good := by
  intro i
  simp [game]

lemma isPureNash_bad (hN : 3 ≤ N) : IsPureNash (game N) bad := by
  refine ⟨?_, ?_⟩
  · intro i
    simp [game]
  · intro i S hS
    have hs : S = good i ∨ S = bad i := by simpa [game] using hS
    rcases hs with rfl | rfl
    · rw [cost_bad hN, cost_deviation hN]
    · simp

/-- Every facility used by player i has at least that player as a user. -/
lemma card_le_cost (Q : Fin N → Finset (Facility N)) (i : Fin N) :
    ((Q i).card : ℝ) ≤ cost (game N) Q i := by
  calc
    ((Q i).card : ℝ) = ∑ e ∈ Q i, (1 : ℝ) := by simp
    _ ≤ cost (game N) Q i := by
      apply Finset.sum_le_sum
      intro e he
      change (1 : ℝ) ≤ (load Q e : ℝ)
      exact_mod_cast (Finset.card_pos.mpr ⟨i, by simp [he]⟩ :
        0 < (univ.filter fun j => e ∈ Q j).card)

lemma cost_profile_ge_two (hN : 3 ≤ N) (Q : Fin N → Finset (Facility N))
    (hQ : IsProfile (game N) Q) (i : Fin N) : 2 ≤ cost (game N) Q i := by
  have hs : Q i = good i ∨ Q i = bad i := by simpa [game] using hQ i
  have hc : 2 ≤ (Q i).card := by
    rcases hs with h | h
    · rw [h, card_good]
    · rw [h, card_bad hN]
      omega
  exact le_trans (by exact_mod_cast hc) (card_le_cost Q i)

lemma sumCost_good : sumCost (game N) good = 2 * (N : ℝ) := by
  simp [sumCost, cost_good]
  ring

lemma sumCost_bad (hN : 3 ≤ N) : sumCost (game N) bad = 5 * (N : ℝ) := by
  simp [sumCost, cost_bad hN]
  ring

lemma optimal_good (hN : 3 ≤ N) (Q : Fin N → Finset (Facility N))
    (hQ : IsProfile (game N) Q) : sumCost (game N) good ≤ sumCost (game N) Q := by
  unfold sumCost
  apply Finset.sum_le_sum
  intro i _
  rw [cost_good]
  exact cost_profile_ge_two hN Q hQ i

end CongestionPoA.AsymSum.Theorem2Construction

open CongestionPoA.AsymSum
open CongestionPoA.AsymSum.Theorem2Construction

theorem solution (N : ℕ) (hN : 3 ≤ N) :
    ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
      (A P : Fin N → Finset E),
      IsLinear G ∧ IsPureNash G A ∧ IsProfile G P ∧
        (∀ Q : Fin N → Finset E, IsProfile G Q → sumCost G P ≤ sumCost G Q) ∧
        0 < sumCost G P ∧ sumCost G A = 5 / 2 * sumCost G P := by
  let : NeZero N := ⟨by omega⟩
  refine ⟨Facility N, inferInstance, inferInstance, game N, bad, good, ?_,
    isPureNash_bad hN, isProfile_good, optimal_good hN, ?_, ?_⟩
  · refine ⟨fun _ => 1, fun _ => 0, ?_, ?_, ?_⟩ <;> simp [game]
  · rw [sumCost_good]
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  · rw [sumCost_bad hN, sumCost_good]
    ring

#print axioms solution
