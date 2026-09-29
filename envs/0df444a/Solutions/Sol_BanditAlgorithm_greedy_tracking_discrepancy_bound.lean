-- Prove2me | solution 1 for BanditAlgorithm.greedy_tracking_discrepancy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T04:21:05.520186+00:00
-- url     : https://prove2.me/submissions/c47357c0-b9c6-499a-b765-1d7dcf229b65

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# The tracking bound: greedy apportionment stays within `k` of its target

`Solutions/TrackingCesaro.lean` derives `T_i(t)/t → α_i` from the hypothesis

  `|T_i(t) − ∑_{s<t} p_i(s)| ≤ C`   for all `i` and `t`,                    (T)

which it takes as given.  This file proves (T), with the explicit constants
`−1` and `k − 1`, for the rule that generates it: at every round play an arm
whose count lags furthest behind its cumulative target,

  `A_t ∈ argmax_i ( ∑_{s<t} p_i(s) − T_i(t) )`.

This is the sampling rule of Garivier & Kaufmann's Track-and-Stop (COLT 2016,
§4, "C-tracking"), and the bound is their Lemma 8.  Nothing probabilistic is
involved: it is a statement about an arbitrary sequence of probability vectors
`p(0), p(1), …` and the deterministic counts the rule produces.

## The argument

Write `D_t(i) = ∑_{s<t} p_i(s) − T_i(t)` for the shortfall of arm `i`.  Two
facts drive everything:

* `∑_i D_t(i) = 0`, because both the targets and the counts sum to `t`;
* `D_{t+1}(i) = D_t(i) + p_i(t) − 1{i = A_t}`.

The lower bound `D_t(i) ≥ −1` is an induction.  An arm other than `A_t` only
gains (`p_i(t) ≥ 0`), so it cannot fall below where it already was.  The played
arm `A_t` loses exactly `1 − p_{A_t}(t) ≤ 1`, but it was the *maximal*
shortfall, and a maximum of numbers summing to zero is nonnegative — so it
starts the round at `D_t(A_t) ≥ 0` and ends it at `≥ −1`.

The upper bound is then free: `D_t(i) = −∑_{j ≠ i} D_t(j) ≤ (k−1)·1`.

So the greedy rule never overshoots its target by more than `1`, and never
lags by more than `k − 1` — both independent of `t` and of the targets.  That
is exactly (T) with `C = k − 1`.

## Why the maximum, and not a threshold

The rule has to be *greedy* rather than "play any arm that is behind": if two
arms are behind and one is always preferred, the other can lag arbitrarily far.
The proof above uses maximality only through `D_t(A_t) ≥ 0`, which is where the
zero-sum identity enters; a threshold rule gives no such handle.
-/

open Finset

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## Cumulative targets -/

/-- `∑_{s<t} p_i(s)`, the total amount of attention the target allocations ask
for arm `i` to have received by round `t`. -/
def cumTarget (p : ℕ → Fin k → ℝ) (t : ℕ) (i : Fin k) : ℝ :=
  ∑ s ∈ Finset.range t, p s i

@[simp]
theorem cumTarget_zero (p : ℕ → Fin k → ℝ) (i : Fin k) : cumTarget p 0 i = 0 := by
  simp [cumTarget]

theorem cumTarget_succ (p : ℕ → Fin k → ℝ) (t : ℕ) (i : Fin k) :
    cumTarget p (t + 1) i = cumTarget p t i + p t i := by
  simp [cumTarget, Finset.sum_range_succ]

/-- The cumulative targets of all arms add up to the number of rounds, because
each round's target is a probability vector. -/
theorem sum_cumTarget (p : ℕ → Fin k → ℝ) (hsum : ∀ s, ∑ i, p s i = 1) (t : ℕ) :
    ∑ i, cumTarget p t i = (t : ℝ) := by
  unfold cumTarget
  rw [Finset.sum_comm]
  simp [hsum]

theorem cumTarget_mono {p : ℕ → Fin k → ℝ} (hnn : ∀ s i, 0 ≤ p s i) (i : Fin k)
    {s t : ℕ} (hst : s ≤ t) : cumTarget p s i ≤ cumTarget p t i := by
  unfold cumTarget
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ ↦ hnn j i)
  exact fun x hx ↦ Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hst)

theorem cumTarget_nonneg {p : ℕ → Fin k → ℝ} (hnn : ∀ s i, 0 ≤ p s i) (t : ℕ)
    (i : Fin k) : 0 ≤ cumTarget p t i :=
  Finset.sum_nonneg fun s _ ↦ hnn s i

/-! ## The tracking rule -/

/-- The counts produced by a rule that always plays an arm of maximal shortfall.

`N t i` is the number of times arm `i` has been played in the first `t` rounds
and `arm t` is the arm played in round `t`.  The three fields say: nothing has
been played at time zero; playing `arm t` increments exactly that arm's count;
and `arm t` maximises the shortfall `cumTarget − N`. -/
structure IsTracking (p : ℕ → Fin k → ℝ) (N : ℕ → Fin k → ℕ) (arm : ℕ → Fin k) :
    Prop where
  init : ∀ i, N 0 i = 0
  step : ∀ t i, N (t + 1) i = N t i + (if i = arm t then 1 else 0)
  greedy : ∀ t i, cumTarget p t i - (N t i : ℝ)
    ≤ cumTarget p t (arm t) - (N t (arm t) : ℝ)

/-- The shortfall of arm `i` after `t` rounds. -/
noncomputable def shortfall (p : ℕ → Fin k → ℝ) (N : ℕ → Fin k → ℕ) (t : ℕ)
    (i : Fin k) : ℝ :=
  cumTarget p t i - (N t i : ℝ)

/-! ## The two structural identities -/

/-- The counts add up to the number of rounds. -/
theorem sum_counts {p : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ} {arm : ℕ → Fin k}
    (h : IsTracking p N arm) (t : ℕ) : ∑ i, (N t i : ℝ) = (t : ℝ) := by
  induction t with
  | zero => simp [h.init]
  | succ t ih =>
      have hstep : ∀ i : Fin k, ((N (t + 1) i : ℝ))
          = (N t i : ℝ) + (if i = arm t then (1 : ℝ) else 0) := by
        intro i
        rw [h.step t i]
        by_cases hi : i = arm t
        · simp [hi]
        · simp [hi]
      calc ∑ i, ((N (t + 1) i : ℝ))
          = ∑ i, ((N t i : ℝ) + (if i = arm t then (1 : ℝ) else 0)) := by
            exact Finset.sum_congr rfl fun i _ ↦ hstep i
        _ = (∑ i, (N t i : ℝ)) + ∑ i, (if i = arm t then (1 : ℝ) else 0) := by
            rw [Finset.sum_add_distrib]
        _ = (t : ℝ) + 1 := by rw [ih]; simp
        _ = ((t + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **The shortfalls sum to zero.**  Both the targets and the counts account for
all `t` rounds, so what one arm is owed another has already been given. -/
theorem sum_shortfall {p : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ} {arm : ℕ → Fin k}
    (h : IsTracking p N arm) (hsum : ∀ s, ∑ i, p s i = 1) (t : ℕ) :
    ∑ i, shortfall p N t i = 0 := by
  unfold shortfall
  rw [Finset.sum_sub_distrib, sum_cumTarget p hsum t, sum_counts h t, sub_self]

/-- The one-round recursion for the shortfall. -/
theorem shortfall_succ {p : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ} {arm : ℕ → Fin k}
    (h : IsTracking p N arm) (t : ℕ) (i : Fin k) :
    shortfall p N (t + 1) i
      = shortfall p N t i + p t i - (if i = arm t then 1 else 0) := by
  unfold shortfall
  rw [cumTarget_succ, h.step t i]
  by_cases hi : i = arm t
  · simp [hi]; ring
  · simp [hi]; ring

/-! ## The played arm is never ahead

A maximum of finitely many reals summing to zero is nonnegative.  Applied to the
shortfalls, this says the arm the rule selects is genuinely behind (or exactly
on) its target — the rule never spends a round on an arm that has already had
more than its share. -/

theorem shortfall_arm_nonneg {p : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ}
    {arm : ℕ → Fin k} (h : IsTracking p N arm) (hsum : ∀ s, ∑ i, p s i = 1)
    (t : ℕ) [NeZero k] : 0 ≤ shortfall p N t (arm t) := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ i : Fin k, shortfall p N t i < 0 := fun i ↦
    lt_of_le_of_lt (h.greedy t i) hcon
  have hlt : ∑ i, shortfall p N t i < 0 := by
    have hne : (Finset.univ : Finset (Fin k)).Nonempty := Finset.univ_nonempty
    exact Finset.sum_neg (fun i _ ↦ hall i) hne
  rw [sum_shortfall h hsum t] at hlt
  exact lt_irrefl _ hlt

/-! ## The lower bound: no arm is ever more than one pull ahead -/

/-- **`shortfall ≥ −1`.**  An arm can only get ahead of its target by the single
pull that put it there, and that pull is only ever spent on an arm that was
behind. -/
theorem neg_one_le_shortfall {p : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ}
    {arm : ℕ → Fin k} [NeZero k] (h : IsTracking p N arm)
    (hnn : ∀ s i, 0 ≤ p s i) (hsum : ∀ s, ∑ i, p s i = 1) (t : ℕ) (i : Fin k) :
    -1 ≤ shortfall p N t i := by
  induction t generalizing i with
  | zero => simp [shortfall, h.init]
  | succ t ih =>
      rw [shortfall_succ h t i]
      by_cases hi : i = arm t
      · -- the played arm: it started the round at or above its target
        have hge : 0 ≤ shortfall p N t (arm t) := shortfall_arm_nonneg h hsum t
        have hgi : 0 ≤ shortfall p N t i := by rw [hi]; exact hge
        simp only [if_pos hi]
        have hp := hnn t i
        linarith
      · simp only [if_neg hi, sub_zero]
        have := ih i
        have hp := hnn t i
        linarith

/-! ## The upper bound: no arm is ever more than `k − 1` pulls behind -/

/-- **`shortfall ≤ k − 1`.**  Immediate from the previous bound and the zero-sum
identity: what one arm is owed, the other `k − 1` are ahead by, and each of them
is ahead by at most one. -/
theorem shortfall_le {p : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ} {arm : ℕ → Fin k}
    [NeZero k] (h : IsTracking p N arm) (hnn : ∀ s i, 0 ≤ p s i)
    (hsum : ∀ s, ∑ i, p s i = 1) (t : ℕ) (i : Fin k) :
    shortfall p N t i ≤ (k : ℝ) - 1 := by
  classical
  have hzero := sum_shortfall h hsum t
  -- split the zero sum into the arm `i` and the rest
  have hsplit : shortfall p N t i
      + ∑ j ∈ Finset.univ.erase i, shortfall p N t j = 0 := by
    rw [← hzero]
    exact Finset.add_sum_erase Finset.univ (fun j ↦ shortfall p N t j)
      (Finset.mem_univ i)
  have hlow : ∀ j ∈ Finset.univ.erase i, (-1 : ℝ) ≤ shortfall p N t j :=
    fun j _ ↦ neg_one_le_shortfall h hnn hsum t j
  have hcard : (Finset.univ.erase i).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  have hbd : (-((k : ℝ) - 1)) ≤ ∑ j ∈ Finset.univ.erase i, shortfall p N t j := by
    have := Finset.sum_le_sum hlow (f := fun _ ↦ (-1 : ℝ))
      (g := fun j ↦ shortfall p N t j)
    rw [Finset.sum_const, hcard] at this
    have hk : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have hk0 : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
      push_cast [Nat.cast_sub hk0]
      ring
    rw [nsmul_eq_mul, hk] at this
    linarith
  linarith

/-! ## The tracking bound (T) -/

/-- **The tracking bound.**  The realised counts stay within `k` of the
cumulative targets, uniformly in the round and in the targets.  This is the
hypothesis `hbd` of `tendsto_trajAllocation_of_tracking`.

The two sides are not symmetric — an arm is at most one pull *ahead* and at most
`k − 1` pulls *behind* — and `k` is simply a bound for both; the sharp two-sided
statements are `count_le_cumTarget_add` and `count_ge_cumTarget_sub`. -/
theorem abs_shortfall_le {p : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ} {arm : ℕ → Fin k}
    [NeZero k] (h : IsTracking p N arm) (hnn : ∀ s i, 0 ≤ p s i)
    (hsum : ∀ s, ∑ i, p s i = 1) (t : ℕ) (i : Fin k) :
    |(N t i : ℝ) - cumTarget p t i| ≤ (k : ℝ) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have hk0 : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    exact_mod_cast hk0
  have hlo := neg_one_le_shortfall h hnn hsum t i
  have hhi := shortfall_le h hnn hsum t i
  unfold shortfall at hlo hhi
  rw [abs_le]
  constructor <;> linarith

/-- The counts, bounded below by the cumulative targets minus `k − 1`. -/
theorem count_ge_cumTarget_sub {p : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ}
    {arm : ℕ → Fin k} [NeZero k] (h : IsTracking p N arm)
    (hnn : ∀ s i, 0 ≤ p s i) (hsum : ∀ s, ∑ i, p s i = 1) (t : ℕ) (i : Fin k) :
    cumTarget p t i - ((k : ℝ) - 1) ≤ (N t i : ℝ) := by
  have := shortfall_le h hnn hsum t i
  unfold shortfall at this
  linarith

/-- The counts, bounded above by the cumulative targets plus one. -/
theorem count_le_cumTarget_add {p : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ}
    {arm : ℕ → Fin k} [NeZero k] (h : IsTracking p N arm)
    (hnn : ∀ s i, 0 ≤ p s i) (hsum : ∀ s, ∑ i, p s i = 1) (t : ℕ) (i : Fin k) :
    (N t i : ℝ) ≤ cumTarget p t i + 1 := by
  have := neg_one_le_shortfall h hnn hsum t i
  unfold shortfall at this
  linarith

end BanditAlgorithm

theorem _root_.solution {k : ℕ} [NeZero k]
    (p : ℕ → Fin k → ℝ) (N : ℕ → Fin k → ℕ) (arm : ℕ → Fin k)
    (hinit : ∀ i, N 0 i = 0)
    (hstep : ∀ t i, N (t + 1) i = N t i + (if i = arm t then 1 else 0))
    (hgreedy : ∀ t i, (∑ s ∈ Finset.range t, p s i) - (N t i : ℝ)
      ≤ (∑ s ∈ Finset.range t, p s (arm t)) - (N t (arm t) : ℝ))
    (hnn : ∀ s i, 0 ≤ p s i) (hsum : ∀ s, ∑ i, p s i = 1) (t : ℕ) (i : Fin k) :
    |(N t i : ℝ) - ∑ s ∈ Finset.range t, p s i| ≤ (k : ℝ) :=
  BanditAlgorithm.abs_shortfall_le ⟨hinit, hstep, hgreedy⟩ hnn hsum t i
