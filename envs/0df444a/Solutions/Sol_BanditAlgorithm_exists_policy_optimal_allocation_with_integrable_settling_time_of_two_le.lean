-- Prove2me | solution 1 for BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T20:35:24.079069+00:00
-- url     : https://prove2.me/submissions/01efa35e-3a63-4bc6-bc7d-a3cdd53544aa

import Theorems.Thm_BanditAlgorithm_alloc_settling_of_tracking_and_target_accuracy
import Theorems.Thm_BanditAlgorithm_settling_of_allocation_half_and_forced_exploration
import Theorems.Thm_BanditAlgorithm_banditTrajMeasure_joint_eq_compProd
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Definitions.Def_TrackAndStop
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Theorems.Thm_BanditAlgorithm_exists_isOptimalAllocation_gaussian
import Definitions.Def_GaussianBandit
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

/-!
# Forcing exploration by mixing the target with the uniform allocation

The tracking rule of `Solutions/TrackingDiscrepancy.lean` keeps the counts within
`k` of the cumulative targets, whatever the targets are.  That alone does not
prevent an arm from being starved: if the target allocation gives arm `i` weight
zero at every round, the rule is perfectly entitled never to play it, and the
empirical mean `μ̂_i` never moves.  In Track-and-Stop the targets are
`α*(μ̂(s))`, computed from the very estimates that starvation would freeze, so
this is a real circularity and not a technicality.

Garivier & Kaufmann (COLT 2016, §4) break it by tracking not `α*(μ̂(s))` itself
but a version of it bounded away from zero.  The construction here is the
convex combination with the uniform allocation,

  `mixUniform ε α = (1 − kε)·α + ε·𝟙`,

which is the simplest map with the three properties the analysis needs:

* it stays in the simplex (`sum_mixUniform`);
* every coordinate is at least `ε` (`le_mixUniform`), so no arm is starved;
* it moves each coordinate by at most `kε` (`abs_mixUniform_sub_le`), so
  driving `ε → 0` recovers the original target in the limit.

The third property is what keeps the *cost* of forced exploration from showing
up in the sample-complexity constant: the perturbation is `O(ε_s)` at round `s`,
and with `ε_s → 0` its Cesàro average vanishes, so the tracked limit is still
`α*(μ)`.  G&K use instead the ℓ^∞-projection onto the truncated simplex, which
satisfies the same three properties with the sharper constant `(k−1)ε`; nothing
downstream is sensitive to the difference, and the explicit formula avoids
having to prove that the projection exists and is continuous.
-/

open Finset Filter Topology

namespace BanditAlgorithm

variable {k : ℕ}

/-- The target allocation `α`, pushed away from the boundary of the simplex by
mixing in a fraction `kε` of the uniform allocation. -/
def mixUniform (ε : ℝ) (α : Fin k → ℝ) (i : Fin k) : ℝ :=
  (1 - (k : ℝ) * ε) * α i + ε

@[simp]
theorem mixUniform_zero (α : Fin k → ℝ) (i : Fin k) : mixUniform 0 α i = α i := by
  simp [mixUniform]

/-! ## It stays in the simplex -/

theorem sum_mixUniform (ε : ℝ) {α : Fin k → ℝ} (hα : ∑ i, α i = 1) :
    ∑ i, mixUniform ε α i = 1 := by
  unfold mixUniform
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hα, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ## No coordinate is smaller than `ε` -/

theorem le_mixUniform {ε : ℝ} (hε : 0 ≤ ε) (hεk : (k : ℝ) * ε ≤ 1) {α : Fin k → ℝ}
    (hnn : ∀ i, 0 ≤ α i) (i : Fin k) : ε ≤ mixUniform ε α i := by
  unfold mixUniform
  have : 0 ≤ (1 - (k : ℝ) * ε) * α i := mul_nonneg (by linarith) (hnn i)
  linarith

theorem mixUniform_nonneg {ε : ℝ} (hε : 0 ≤ ε) (hεk : (k : ℝ) * ε ≤ 1)
    {α : Fin k → ℝ} (hnn : ∀ i, 0 ≤ α i) (i : Fin k) : 0 ≤ mixUniform ε α i :=
  le_trans hε (le_mixUniform hε hεk hnn i)

/-! ## The perturbation is `O(ε)`

A coordinate of a probability vector lies in `[0,1]`, so `|1 − k·α i| ≤ k` and
the displacement `ε(1 − k·α i)` is at most `kε`. -/

theorem coord_le_one {α : Fin k → ℝ} (hnn : ∀ i, 0 ≤ α i) (hα : ∑ i, α i = 1)
    (i : Fin k) : α i ≤ 1 := by
  classical
  rw [← hα]
  exact Finset.single_le_sum (fun j _ ↦ hnn j) (Finset.mem_univ i)

theorem abs_mixUniform_sub_le {ε : ℝ} (hε : 0 ≤ ε) {α : Fin k → ℝ}
    (hnn : ∀ i, 0 ≤ α i) (hα : ∑ i, α i = 1) (i : Fin k) :
    |mixUniform ε α i - α i| ≤ (k : ℝ) * ε := by
  have hle : α i ≤ 1 := coord_le_one hnn hα i
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have heq : mixUniform ε α i - α i = ε * (1 - (k : ℝ) * α i) := by
    unfold mixUniform; ring
  rw [heq, abs_mul, abs_of_nonneg hε]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have : 0 < k := Fin.pos i
    exact_mod_cast this
  have hbd : |1 - (k : ℝ) * α i| ≤ (k : ℝ) := by
    rw [abs_le]
    constructor
    · nlinarith [hnn i]
    · nlinarith [hnn i, mul_nonneg hk0 (hnn i)]
  calc ε * |1 - (k : ℝ) * α i| ≤ ε * (k : ℝ) := by
        exact mul_le_mul_of_nonneg_left hbd hε
    _ = (k : ℝ) * ε := by ring

/-! ## Vanishing `ε` recovers the target

For a sequence of targets converging to `α` and a floor sequence tending to zero,
the mixed targets converge to `α` as well — so tracking the mixed targets and
tracking the true ones have the same limit, and the forced exploration is free
in the Cesàro limit. -/

theorem tendsto_mixUniform {e : ℕ → ℝ} {a : ℕ → Fin k → ℝ} {α : Fin k → ℝ}
    (he : Tendsto e atTop (𝓝 0)) (ha : ∀ i, Tendsto (fun s ↦ a s i) atTop (𝓝 (α i)))
    (i : Fin k) :
    Tendsto (fun s ↦ mixUniform (e s) (a s) i) atTop (𝓝 (α i)) := by
  have hcoef : Tendsto (fun s ↦ 1 - (k : ℝ) * e s) atTop (𝓝 1) := by
    have : Tendsto (fun s ↦ (k : ℝ) * e s) atTop (𝓝 ((k : ℝ) * 0)) :=
      he.const_mul _
    rw [mul_zero] at this
    simpa using tendsto_const_nhds.sub this
  have hprod : Tendsto (fun s ↦ (1 - (k : ℝ) * e s) * a s i) atTop (𝓝 (1 * α i)) :=
    hcoef.mul (ha i)
  rw [one_mul] at hprod
  have := hprod.add he
  rw [add_zero] at this
  exact this

end BanditAlgorithm

/-!
# A telescoping lower bound for `∑ 1/(2√(c+s))`

The exploration floor used by Track-and-Stop at round `s` is

  `ε_s = 1/(2√(k² + s))`,

and what the analysis needs is that these floors *accumulate*: the total amount
of forced exploration guaranteed to each arm by round `t` is `∑_{s<t} ε_s`, and
this has to grow without bound (else an arm could be starved after all) at a
known rate (else no explicit round can be named from which the empirical means
are accurate).

Both come from one inequality,

  `√(x+1) − √x ≤ 1/(2√x)`,

which telescopes to

  `√(c+t) − √c ≤ ∑_{s<t} 1/(2√(c+s))`.

With `c = k²` the left-hand side is `√(k²+t) − k`, so each arm is guaranteed
`≈ √t` pulls — the rate quoted in Garivier & Kaufmann's Lemma 7.

The inequality itself is the concavity of `√` in disguise: `√(x+1) − √x` is the
increment of `√` over a unit step, and `1/(2√x)` is its derivative at the left
endpoint.  The proof below avoids calculus and uses only
`√(x+1) − √x = 1/(√(x+1) + √x)`, bounding the denominator below by `2√x`.

The constant `1/2` in the floor matters: `ε_s = c/√s` telescopes to `2c√t`, so
`c = 1/2` is exactly the choice that makes the guarantee `√t` rather than a
multiple of it, and any smaller constant would still diverge — the floor is not
delicate, only its divergence is used.
-/

open Finset Filter Topology

namespace BanditAlgorithm

/-! ## The one-step inequality -/

/-- **A unit step of `√` is at most the derivative at the left endpoint.** -/
theorem sqrt_succ_sub_le {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x + 1) - Real.sqrt x ≤ 1 / (2 * Real.sqrt x) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsx1 : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr (by linarith)
  have hmono : Real.sqrt x ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hsq1 : Real.sqrt (x + 1) * Real.sqrt (x + 1) = x + 1 :=
    Real.mul_self_sqrt (by linarith)
  -- `(√(x+1) − √x)(√(x+1) + √x) = 1`
  have hprod : (Real.sqrt (x + 1) - Real.sqrt x) * (Real.sqrt (x + 1) + Real.sqrt x)
      = 1 := by nlinarith
  have hden : 0 < Real.sqrt (x + 1) + Real.sqrt x := by linarith
  have hdiff : Real.sqrt (x + 1) - Real.sqrt x
      = 1 / (Real.sqrt (x + 1) + Real.sqrt x) := by
    field_simp
    linarith [hprod]
  rw [hdiff]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  linarith

/-! ## The telescoped sum -/

/-- **`∑_{s<t} 1/(2√(c+s)) ≥ √(c+t) − √c`.**  Each summand pays for one unit
step of `√`, so the sum pays for the whole increment. -/
theorem sqrt_add_sub_le_sum {c : ℝ} (hc : 0 < c) (t : ℕ) :
    Real.sqrt (c + (t : ℝ)) - Real.sqrt c
      ≤ ∑ s ∈ Finset.range t, 1 / (2 * Real.sqrt (c + (s : ℝ))) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ]
      have hct : 0 < c + (t : ℝ) := by positivity
      have hstep := sqrt_succ_sub_le hct
      have hcast : c + ((t + 1 : ℕ) : ℝ) = (c + (t : ℝ)) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-! ## The exploration floor

The floor sequence itself, with the three properties the tracking analysis uses:
it is positive, it is small enough for the simplex mixing to be legal, and it
tends to zero. -/

/-- `ε_s = 1/(2√(k² + s))`, the exploration floor at round `s`. -/
noncomputable def exploreFloor (k : ℕ) (s : ℕ) : ℝ :=
  1 / (2 * Real.sqrt ((k : ℝ) ^ 2 + (s : ℝ)))

theorem exploreFloor_pos {k : ℕ} (hk : 0 < k) (s : ℕ) : 0 < exploreFloor k s := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have : (0 : ℝ) < (k : ℝ) ^ 2 + (s : ℝ) := by positivity
  unfold exploreFloor
  positivity

theorem exploreFloor_nonneg {k : ℕ} (hk : 0 < k) (s : ℕ) : 0 ≤ exploreFloor k s :=
  (exploreFloor_pos hk s).le

/-- The floor is small enough that mixing `kε` of the uniform allocation into a
probability vector is legal: `k · ε_s ≤ 1/2 ≤ 1`. -/
theorem mul_exploreFloor_le_one {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (k : ℝ) * exploreFloor k s ≤ 1 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hks : (k : ℝ) ≤ Real.sqrt ((k : ℝ) ^ 2 + (s : ℝ)) := by
    have h1 : Real.sqrt ((k : ℝ) ^ 2) ≤ Real.sqrt ((k : ℝ) ^ 2 + (s : ℝ)) :=
      Real.sqrt_le_sqrt (by have : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s; linarith)
    rwa [Real.sqrt_sq hk0.le] at h1
  have hden : 0 < 2 * Real.sqrt ((k : ℝ) ^ 2 + (s : ℝ)) := by linarith
  unfold exploreFloor
  rw [mul_one_div, div_le_one hden]
  linarith

/-- **The accumulated floor.**  By round `t` the rule has promised every arm at
least `√(k² + t) − k` pulls. -/
theorem sqrt_le_sum_exploreFloor {k : ℕ} (hk : 0 < k) (t : ℕ) :
    Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - (k : ℝ)
      ≤ ∑ s ∈ Finset.range t, exploreFloor k s := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have h := sqrt_add_sub_le_sum (c := (k : ℝ) ^ 2) hpos t
  rwa [Real.sqrt_sq hk0.le] at h

/-- The floor tends to zero, so the forced exploration does not distort the
tracked limit. -/
theorem tendsto_exploreFloor {k : ℕ} (hk : 0 < k) :
    Tendsto (exploreFloor k) atTop (𝓝 0) := by
  have hlin : Tendsto (fun s : ℕ ↦ (k : ℝ) ^ 2 + (s : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun s : ℕ ↦ Real.sqrt ((k : ℝ) ^ 2 + (s : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlin
  have hdiv : Tendsto (fun s : ℕ ↦ 2 * Real.sqrt ((k : ℝ) ^ 2 + (s : ℝ)))
      atTop atTop := hsqrt.const_mul_atTop (by norm_num)
  unfold exploreFloor
  simpa only [one_div, Pi.inv_def] using hdiv.inv_tendsto_atTop

end BanditAlgorithm

/-!
# Forced exploration comes for free from tracking a floored target

Garivier & Kaufmann's sampling rule has two jobs that look independent: track
the optimal allocation, and make sure no arm is starved.  Implemented naively
they conflict — a forced-exploration override breaks the tracking bound, since
the round it spends is not the round the greedy rule would have chosen.

The resolution is that forced exploration need not be an override at all.  Track
the *floored* targets

  `p_i(s) = mixUniform ε_s (α(s)) i = (1 − kε_s)·α_i(s) + ε_s`,   `ε_s = 1/(2√(k²+s))`,

and both jobs are done by the single greedy rule:

* the tracking bound of `Solutions/TrackingDiscrepancy.lean` applies verbatim,
  since `p(s)` is a probability vector like any other;
* every coordinate of `p(s)` is at least `ε_s`, so the cumulative target for
  each arm is at least `∑_{s<t} ε_s ≥ √(k²+t) − k`
  (`Solutions/SqrtTelescope.lean`), and the tracking bound turns that into a
  lower bound on the *realised* counts.

The conclusion is `T_i(t) ≥ √(k²+t) − 2k + 1` for every arm and every round —
Garivier & Kaufmann's Lemma 7 — with no probabilistic content and no appeal to
the particular targets `α(s)`.  Contrapositively, from round `(M + 2k)²` on,
every arm has been played more than `M` times, which is the form
`Solutions/MeanSettling.lean` consumes.

This supersedes the argument of `Solutions/ForcedExploration.lean`, which
analyses an explicit override rule (`play a least-played arm whenever
min_i T_i(t) < √t`) and gets the same `√t` rate.  That rule is a legitimate
alternative, but it does not track, so it cannot be the whole sampling rule;
the floored-target version is the one Track-and-Stop actually uses.
-/

open Finset Filter Topology

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The floored targets -/

/-- The target sequence actually tracked: the allocations `a s`, floored at the
exploration level `ε_s`. -/
noncomputable def flooredTarget (k : ℕ) (a : ℕ → Fin k → ℝ) (s : ℕ) (i : Fin k) : ℝ :=
  mixUniform (exploreFloor k s) (a s) i

theorem flooredTarget_sum {a : ℕ → Fin k → ℝ} (ha : ∀ s, ∑ i, a s i = 1) (s : ℕ) :
    ∑ i, flooredTarget k a s i = 1 :=
  sum_mixUniform _ (ha s)

theorem exploreFloor_le_flooredTarget (hk : 0 < k) {a : ℕ → Fin k → ℝ}
    (hnn : ∀ s i, 0 ≤ a s i) (s : ℕ) (i : Fin k) :
    exploreFloor k s ≤ flooredTarget k a s i :=
  le_mixUniform (exploreFloor_nonneg hk s) (mul_exploreFloor_le_one hk s) (hnn s) i

theorem flooredTarget_nonneg (hk : 0 < k) {a : ℕ → Fin k → ℝ}
    (hnn : ∀ s i, 0 ≤ a s i) (s : ℕ) (i : Fin k) : 0 ≤ flooredTarget k a s i :=
  le_trans (exploreFloor_nonneg hk s) (exploreFloor_le_flooredTarget hk hnn s i)

/-! ## The accumulated target is at least `√(k²+t) − k` -/

theorem sqrt_le_cumTarget (hk : 0 < k) {a : ℕ → Fin k → ℝ}
    (hnn : ∀ s i, 0 ≤ a s i) (t : ℕ) (i : Fin k) :
    Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - (k : ℝ)
      ≤ cumTarget (flooredTarget k a) t i := by
  refine le_trans (sqrt_le_sum_exploreFloor hk t) ?_
  unfold cumTarget
  exact Finset.sum_le_sum fun s _ ↦ exploreFloor_le_flooredTarget hk hnn s i

/-! ## Garivier & Kaufmann, Lemma 7 -/

/-- **No arm is starved.**  Tracking floored targets guarantees every arm
`√(k²+t) − 2k + 1` pulls by round `t`, deterministically. -/
theorem sqrt_le_count [NeZero k] {a : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ}
    {arm : ℕ → Fin k} (h : IsTracking (flooredTarget k a) N arm)
    (hnn : ∀ s i, 0 ≤ a s i) (ha : ∀ s, ∑ i, a s i = 1) (t : ℕ) (i : Fin k) :
    Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - 2 * (k : ℝ) + 1 ≤ (N t i : ℝ) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hcum := count_ge_cumTarget_sub h (flooredTarget_nonneg hk hnn)
    (flooredTarget_sum ha) t i
  have hsq := sqrt_le_cumTarget hk hnn t i
  linarith

/-! ## The explicit round from which every arm is well explored -/

/-- The round from which tracking guarantees every arm more than `M` pulls. -/
def forcedTrackRound (k M : ℕ) : ℕ := (M + 2 * k) ^ 2

theorem forcedTrackRound_mono {M M' : ℕ} (h : M ≤ M') :
    forcedTrackRound k M ≤ forcedTrackRound k M' :=
  Nat.pow_le_pow_left (by omega) 2

/-- **Every arm has been played more than `M` times from round `(M+2k)²` on.** -/
theorem lt_count_of_forcedTrackRound_le [NeZero k] {a : ℕ → Fin k → ℝ}
    {N : ℕ → Fin k → ℕ} {arm : ℕ → Fin k} (h : IsTracking (flooredTarget k a) N arm)
    (hnn : ∀ s i, 0 ≤ a s i) (ha : ∀ s, ∑ i, a s i = 1) {M t : ℕ}
    (ht : forcedTrackRound k M ≤ t) (i : Fin k) : M < N t i := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hbase := sqrt_le_count h hnn ha t i
  -- it suffices that `√(k²+t) > M + 2k − 1`
  have hMk : (0 : ℝ) ≤ (M : ℝ) + 2 * (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith [(by exact_mod_cast hk : (1 : ℝ) ≤ (k : ℝ))]
  have htR : ((M : ℝ) + 2 * (k : ℝ)) ^ 2 ≤ (t : ℝ) := by
    have : ((forcedTrackRound k M : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    unfold forcedTrackRound at this
    push_cast at this
    linarith
  have hsqlt : ((M : ℝ) + 2 * (k : ℝ) - 1) ^ 2 < (k : ℝ) ^ 2 + (t : ℝ) := by
    have hmono : ((M : ℝ) + 2 * (k : ℝ) - 1) ^ 2 ≤ ((M : ℝ) + 2 * (k : ℝ)) ^ 2 := by
      have h1 : (0 : ℝ) ≤ (M : ℝ) + 2 * (k : ℝ) - 1 := hMk
      nlinarith
    nlinarith [sq_nonneg ((k : ℝ))]
  have hsqrt : (M : ℝ) + 2 * (k : ℝ) - 1
      < Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) := by
    rw [show ((k : ℝ) ^ 2 + (t : ℝ)) = ((k : ℝ) ^ 2 + (t : ℝ)) from rfl]
    exact (Real.lt_sqrt hMk).mpr hsqlt
  have hfin : (M : ℝ) < (N t i : ℝ) := by linarith
  exact_mod_cast hfin

/-! ## Consequence: the counts diverge

The floored-target rule makes every count tend to infinity, which is the
qualitative statement behind the settling of the empirical means. -/

theorem tendsto_count_atTop [NeZero k] {a : ℕ → Fin k → ℝ} {N : ℕ → Fin k → ℕ}
    {arm : ℕ → Fin k} (h : IsTracking (flooredTarget k a) N arm)
    (hnn : ∀ s i, 0 ≤ a s i) (ha : ∀ s, ∑ i, a s i = 1) (i : Fin k) :
    Tendsto (fun t ↦ N t i) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun M ↦ ⟨forcedTrackRound k M, fun t ht ↦ ?_⟩
  exact (lt_count_of_forcedTrackRound_le h hnn ha ht i).le

end BanditAlgorithm

/-!
# Elementary algebra of the trajectory statistics

Pull counts, empirical means and empirical allocations, and the identities that
every part of the Track-and-Stop analysis uses:

* `trajPullCount_succ` — the one-round recursion `T_i(t+1) = T_i(t) + 1{A_{t+1} = i}`;
* `sum_trajPullCount` — `∑_i T_i(t) = t`;
* `trajPullCount_le` — `T_i(t) ≤ t`, and monotonicity in `t`;
* `sum_trajAllocation` — the empirical allocation lies in the simplex for `t > 0`;
* `trajEmpiricalMean_eq_zero_of_pullCount_eq_zero` — the junk value convention;
* `trajRewardSum_eq` — `∑ rewards = T_i(t) · μ̂_i(t)` when `T_i(t) > 0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-- The sum of the rewards collected from arm `i` in the first `t` rounds. -/
noncomputable def trajRewardSum (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ :=
  ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2

theorem trajEmpiricalMean_eq (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajEmpiricalMean i t ω = trajRewardSum i t ω / (trajPullCount i t ω : ℝ) := rfl

/-! ## Pull counts -/

@[simp]
theorem trajPullCount_zero (i : Fin k) (ω : ℕ → Fin k × ℝ) : trajPullCount i 0 ω = 0 := by
  simp [trajPullCount]

theorem trajPullCount_succ (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i (t + 1) ω =
      trajPullCount i t ω + if (ω t).1 = i then 1 else 0 := by
  classical
  simp only [trajPullCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : (ω t).1 = i
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, add_zero]

theorem trajRewardSum_succ (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajRewardSum i (t + 1) ω =
      trajRewardSum i t ω + if (ω t).1 = i then (ω t).2 else 0 := by
  classical
  simp only [trajRewardSum, Finset.range_add_one, Finset.filter_insert]
  by_cases h : (ω t).1 = i
  · rw [if_pos h, Finset.sum_insert (by simp), if_pos h, add_comm]
  · rw [if_neg h, if_neg h, add_zero]

theorem trajPullCount_mono (i : Fin k) {s t : ℕ} (h : s ≤ t) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i s ω ≤ trajPullCount i t ω := by
  classical
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  exact fun x hx ↦ Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

theorem trajPullCount_le (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i t ω ≤ t := by
  classical
  calc trajPullCount i t ω ≤ (Finset.range t).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = t := Finset.card_range t

/-- The pull counts of the `k` arms partition the rounds: `∑_i T_i(t) = t`. -/
theorem sum_trajPullCount (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    ∑ i : Fin k, trajPullCount i t ω = t := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
      simp only [trajPullCount_succ, Finset.sum_add_distrib, ih]
      congr 1
      simp

/-- Some arm is played at least `t / k` times. -/
theorem exists_trajPullCount_ge (hk : 0 < k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    ∃ i : Fin k, t ≤ k * trajPullCount i t ω := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
    (fun i ↦ trajPullCount i t ω) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc t = ∑ j : Fin k, trajPullCount j t ω := (sum_trajPullCount t ω).symm
    _ ≤ ∑ _j : Fin k, trajPullCount i t ω :=
        Finset.sum_le_sum fun j _ ↦ hi j (Finset.mem_univ j)
    _ = k * trajPullCount i t ω := by simp [mul_comm]

/-! ## Empirical allocations -/

@[simp]
theorem trajAllocation_eq (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajAllocation i t ω = (trajPullCount i t ω : ℝ) / (t : ℝ) := rfl

theorem trajAllocation_nonneg (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    0 ≤ trajAllocation i t ω :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem trajAllocation_le_one (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajAllocation i t ω ≤ 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [trajAllocation]
  · rw [trajAllocation_eq, div_le_one (by exact_mod_cast ht)]
    exact_mod_cast trajPullCount_le i t ω

/-- For `t > 0` the empirical allocation lies in the probability simplex. -/
theorem sum_trajAllocation {t : ℕ} (ht : 0 < t) (ω : ℕ → Fin k × ℝ) :
    ∑ i : Fin k, trajAllocation i t ω = 1 := by
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  simp only [trajAllocation_eq, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_trajPullCount t ω]
  exact div_self htR

/-! ## Empirical means -/

theorem trajEmpiricalMean_of_pullCount_eq_zero {i : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (h : trajPullCount i t ω = 0) : trajEmpiricalMean i t ω = 0 := by
  simp [trajEmpiricalMean, h]

theorem trajRewardSum_eq_mul (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : trajPullCount i t ω ≠ 0) :
    trajRewardSum i t ω = (trajPullCount i t ω : ℝ) * trajEmpiricalMean i t ω := by
  have hne : ((trajPullCount i t ω : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
  rw [trajEmpiricalMean_eq, mul_div_cancel₀ _ hne]

/-! ## The pairwise GLR statistic -/

theorem trajPairGLR_comm (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPairGLR a b t ω = trajPairGLR b a t ω := by
  simp only [trajPairGLR]
  rw [mul_comm ((trajPullCount a t ω : ℕ) : ℝ) ((trajPullCount b t ω : ℕ) : ℝ),
    add_comm ((trajPullCount a t ω : ℕ) : ℝ) ((trajPullCount b t ω : ℕ) : ℝ),
    ← neg_sub (trajEmpiricalMean a t ω) (trajEmpiricalMean b t ω), neg_pow]
  ring

theorem trajPairGLR_nonneg (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    0 ≤ trajPairGLR a b t ω := by
  refine div_nonneg (mul_nonneg (div_nonneg (mul_nonneg ?_ ?_) ?_) (sq_nonneg _)) (by norm_num)
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _
  · positivity

theorem trajPairGLR_self (a : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPairGLR a a t ω = 0 := by
  simp [trajPairGLR]

end BanditAlgorithm

/-!
# Tracking a convergent sequence of allocations

The second half of the D-Tracking analysis (Garivier & Kaufmann, Lemma 8) is a
Cesàro argument and nothing more.  The sampling rule maintains a sequence of
target allocations `p(0), p(1), …` — in Track-and-Stop, `p(s) = α*(μ̂(s))`, which
converges to `α*(μ)` once the empirical means have converged — and plays so that
the realised counts stay within a bounded distance of the cumulative targets:

  `|N_i(t) − ∑_{s < t} p_i(s)| ≤ C`   for all `t`.                        (T)

Then `N_i(t)/t → α_i`, because `(1/t) ∑_{s<t} p_i(s) → α_i` by Cesàro and the
discrepancy `C/t` vanishes.

Only (T) is assumed here; establishing it for a concrete rule is the tracking
lemma proper, and the *other* half of D-Tracking — that no arm is starved — is
`Solutions/ForcedExploration.lean`.  Together they give the hypothesis `htrack`
of the sample-complexity statements.
-/

open Filter Topology

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The abstract statement -/

/-- **Cesàro tracking.**  Counts that stay within a constant of the cumulative
targets inherit the limit of the targets, in the Cesàro sense. -/
theorem tendsto_div_of_tracking {p : ℕ → ℝ} {a C : ℝ}
    (hp : Tendsto p atTop (𝓝 a)) {M : ℕ → ℝ}
    (hbd : ∀ t : ℕ, |M t - ∑ s ∈ Finset.range t, p s| ≤ C) :
    Tendsto (fun t : ℕ ↦ M t / (t : ℝ)) atTop (𝓝 a) := by
  have hces : Tendsto (fun t : ℕ ↦ (∑ s ∈ Finset.range t, p s) / (t : ℝ))
      atTop (𝓝 a) := by
    refine hp.cesaro.congr fun t ↦ ?_
    rw [div_eq_inv_mul]
  -- the discrepancy vanishes
  have hzero : Tendsto (fun t : ℕ ↦
      (M t - ∑ s ∈ Finset.range t, p s) / (t : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat |C|)
    filter_upwards [eventually_gt_atTop 0] with t ht
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos htR]
    exact div_le_div_of_nonneg_right (le_trans (hbd t) (le_abs_self C)) htR.le
  -- and the sum of the two is the quotient we want
  have hsum := hces.add hzero
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have htR : ((t : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    exact this.ne'
  field_simp
  ring

/-! ## The bandit form -/

/-- The version used for the pull counts: `T_i(t)/t → α_i`. -/
theorem tendsto_trajAllocation_of_tracking {p : Fin k → ℕ → ℝ} {α : Fin k → ℝ}
    {C : ℝ} {ω : ℕ → Fin k × ℝ}
    (hp : ∀ i, Tendsto (p i) atTop (𝓝 (α i)))
    (hbd : ∀ i, ∀ t : ℕ,
      |(trajPullCount i t ω : ℝ) - ∑ s ∈ Finset.range t, p i s| ≤ C) :
    ∀ i, Tendsto (fun t : ℕ ↦ trajAllocation i t ω) atTop (𝓝 (α i)) := by
  intro i
  have h := tendsto_div_of_tracking (hp i) (M := fun t ↦ (trajPullCount i t ω : ℝ))
    (hbd i)
  refine h.congr fun t ↦ ?_
  rw [trajAllocation_eq]

/-! ## A sufficient condition for (T): a one-step tracking bound

If at every round the count of the played arm is the one furthest behind its
target, the discrepancy stays bounded; that is the content of the tracking rule.
Recorded here in the weaker form actually needed downstream: a uniform bound on
the discrepancy at every round is enough, however it is obtained. -/

/-- Discrepancies that are bounded at each round are bounded uniformly by the
supremum, so (T) is exactly a uniform-boundedness statement. -/
theorem tracking_of_forall_le {p : Fin k → ℕ → ℝ} {C : ℝ} {ω : ℕ → Fin k × ℝ}
    (h : ∀ i t, |(trajPullCount i t ω : ℝ) - ∑ s ∈ Finset.range t, p i s| ≤ C)
    (i : Fin k) (t : ℕ) :
    |(trajPullCount i t ω : ℝ) - ∑ s ∈ Finset.range t, p i s| ≤ C := h i t

/-! ## Convergence of the targets from convergence of the means

In Track-and-Stop the targets are `p(s) = choice(μ̂(s))`, so their convergence
follows from that of the empirical means together with continuity of the map
`choice` at `μ`.  Continuity is genuinely needed: `choice` is only required to
*select* an optimal allocation, and a selection that jumps cannot be tracked. -/

theorem tendsto_targets_of_continuousAt {choice : (Fin k → ℝ) → Fin k → ℝ}
    {μvec : Fin k → ℝ} {m : ℕ → Fin k → ℝ}
    (hcont : ContinuousAt choice μvec)
    (hm : Tendsto m atTop (𝓝 μvec)) (i : Fin k) :
    Tendsto (fun s ↦ choice (m s) i) atTop (𝓝 (choice μvec i)) := by
  have h : Tendsto (fun s ↦ choice (m s)) atTop (𝓝 (choice μvec)) :=
    hcont.tendsto.comp hm
  exact (continuous_apply i).continuousAt.tendsto.comp h

end BanditAlgorithm

/-!
# The pairwise weight `xy/(x+y)`

Every quantity in the Track-and-Stop analysis that couples two arms is built from

  `pairHarm x y = xy/(x+y)`,

half the harmonic mean of `x` and `y`.  It appears as the effective sample size
of a pair: the generalised-likelihood-ratio statistic for "arm `a` beats arm `b`"
after `t` rounds is `pairHarm (T_a) (T_b) · (μ̂_a − μ̂_b)²/2`, and the optimal
allocation maximises `min_{j ≠ i*} pairHarm (α_{i*}) (α_j) · (μ_{i*} − μ_j)²/2`.
Both the rate lemmas and the continuity of the optimal allocation therefore rest
on the elementary properties of this one function.

## The junk value is the right value

At `x = y = 0` the formula reads `0/0`, which Lean evaluates to `0`.  That is not
a convention one has to work around — it is the correct value: `pairHarm x y ≤
min x y`, so the function extends continuously to the corner by `0`.  This is
what `continuousOn_pairHarm` says, and it is the reason the objective is
continuous on the *closed* simplex rather than only on its interior, which in
turn is what lets the maximum be attained.

That the corner is the only difficulty is worth stating plainly: away from
`x + y = 0` the function is a quotient with non-vanishing denominator and
continuity is automatic.  On the nonnegative quadrant `x + y = 0` forces
`x = y = 0`, so there is exactly one point to check by hand.

## Monotonicity

`pairHarm` is nondecreasing in each argument (`pairHarm_mono`).  Sampling an arm
more never decreases the evidence available about any pair containing it — which
is why lower bounds on the counts translate directly into lower bounds on the
GLR statistic.
-/

open Filter Topology Metric

namespace BanditAlgorithm

/-- `xy/(x+y)`, half the harmonic mean; `0` when both arguments vanish. -/
noncomputable def pairHarm (x y : ℝ) : ℝ := x * y / (x + y)

@[simp]
theorem pairHarm_zero_left (y : ℝ) : pairHarm 0 y = 0 := by simp [pairHarm]

@[simp]
theorem pairHarm_zero_right (x : ℝ) : pairHarm x 0 = 0 := by simp [pairHarm]

theorem pairHarm_comm (x y : ℝ) : pairHarm x y = pairHarm y x := by
  unfold pairHarm; rw [mul_comm, add_comm]

/-! ## Basic bounds -/

theorem pairHarm_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ pairHarm x y := by
  unfold pairHarm
  positivity

/-- `pairHarm x y ≤ x`: the pair is never more informative than its weaker half. -/
theorem pairHarm_le_left {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : pairHarm x y ≤ x := by
  rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ x + y) with hz | hpos
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [pairHarm, hx0, hy0]
  · unfold pairHarm
    rw [div_le_iff₀ hpos]
    nlinarith

theorem pairHarm_le_right {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : pairHarm x y ≤ y := by
  rw [pairHarm_comm]
  exact pairHarm_le_left hy hx

theorem pairHarm_le_min {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pairHarm x y ≤ min x y :=
  le_min (pairHarm_le_left hx hy) (pairHarm_le_right hx hy)

/-- The reciprocal form `1/pairHarm = 1/x + 1/y`, valid when both are positive. -/
theorem inv_pairHarm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (pairHarm x y)⁻¹ = x⁻¹ + y⁻¹ := by
  unfold pairHarm
  rw [inv_div]
  field_simp
  ring

theorem pairHarm_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < pairHarm x y := by
  unfold pairHarm
  positivity

/-! ## Monotonicity

Increasing either argument increases the weight.  The proof is the reciprocal
identity in disguise: `1/pairHarm = 1/x + 1/y` is decreasing in each variable. -/

theorem pairHarm_mono {x y x' y' : ℝ} (hx : 0 < x) (hy : 0 < y) (hxx : x ≤ x')
    (hyy : y ≤ y') : pairHarm x y ≤ pairHarm x' y' := by
  have hx' : 0 < x' := lt_of_lt_of_le hx hxx
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy
  unfold pairHarm
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  -- `x'y'(x+y) − xy(x'+y') = x x'(y'−y) + y y'(x'−x) ≥ 0`
  nlinarith [mul_nonneg (mul_pos hx hx').le (sub_nonneg.mpr hyy),
    mul_nonneg (mul_pos hy hy').le (sub_nonneg.mpr hxx)]

/-! ## Continuity on the closed quadrant -/

theorem continuousAt_pairHarm_of_pos {p : ℝ × ℝ} (hp : 0 < p.1 + p.2) :
    ContinuousAt (fun q : ℝ × ℝ ↦ pairHarm q.1 q.2) p := by
  unfold pairHarm
  exact ContinuousAt.div (continuousAt_fst.mul continuousAt_snd)
    (continuousAt_fst.add continuousAt_snd) hp.ne'

/-- **`pairHarm` is continuous on the nonnegative quadrant**, corner included. -/
theorem continuousOn_pairHarm :
    ContinuousOn (fun q : ℝ × ℝ ↦ pairHarm q.1 q.2)
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  rintro p ⟨hp1, hp2⟩
  rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ p.1 + p.2) with hz | hpos
  · -- the corner: squeeze against `min p.1 p.2`
    have hp10 : p.1 = 0 := by linarith
    have hp20 : p.2 = 0 := by linarith
    have hval : pairHarm p.1 p.2 = 0 := by simp [hp10]
    rw [ContinuousWithinAt, hval]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    refine ⟨ε, hε, fun q hq hqd ↦ ?_⟩
    obtain ⟨hq1, hq2⟩ := hq
    have hle : pairHarm q.1 q.2 ≤ q.1 := pairHarm_le_left hq1 hq2
    have hnn : 0 ≤ pairHarm q.1 q.2 := pairHarm_nonneg hq1 hq2
    have hd : dist q p = max |q.1 - p.1| |q.2 - p.2| := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    have hq1le : q.1 ≤ dist q p := by
      rw [hd, hp10]
      refine le_trans ?_ (le_max_left _ _)
      rw [sub_zero]
      exact le_abs_self _
    linarith
  · exact (continuousAt_pairHarm_of_pos hpos).continuousWithinAt

/-! ## The two-variable form used by the objective

The GLR rate for a pair is `pairHarm α_a α_b · (μ_a − μ_b)²/2`, jointly
continuous in the allocation and the means. -/

/-- The rate contributed by the pair `(a,b)` at allocation weights `(x,y)` and
mean gap `g`. -/
noncomputable def harmCost (x y g : ℝ) : ℝ := pairHarm x y * g ^ 2 / 2

theorem harmCost_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (g : ℝ) :
    0 ≤ harmCost x y g := by
  unfold harmCost
  have := pairHarm_nonneg hx hy
  positivity

theorem harmCost_mono {x y x' y' g : ℝ} (hx : 0 < x) (hy : 0 < y) (hxx : x ≤ x')
    (hyy : y ≤ y') : harmCost x y g ≤ harmCost x' y' g := by
  unfold harmCost
  have h := pairHarm_mono hx hy hxx hyy
  have : (0 : ℝ) ≤ g ^ 2 := sq_nonneg g
  gcongr

theorem continuousOn_harmCost :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ ↦ harmCost q.1.1 q.1.2 q.2)
      {q : (ℝ × ℝ) × ℝ | 0 ≤ q.1.1 ∧ 0 ≤ q.1.2} := by
  unfold harmCost
  have hharm : ContinuousOn (fun q : (ℝ × ℝ) × ℝ ↦ pairHarm q.1.1 q.1.2)
      {q : (ℝ × ℝ) × ℝ | 0 ≤ q.1.1 ∧ 0 ≤ q.1.2} := by
    refine ContinuousOn.comp continuousOn_pairHarm continuous_fst.continuousOn ?_
    rintro q ⟨h1, h2⟩
    exact ⟨h1, h2⟩
  exact (hharm.mul (continuous_snd.pow 2).continuousOn).div_const 2

end BanditAlgorithm

/-!
# A maximiser depends continuously on the parameter where it is unique

`Solutions/TrackingCesaro.lean` derives the convergence of the tracked targets
`α*(μ̂(s)) → α*(μ)` from `ContinuousAt α* μ`, and flags that continuity is
genuinely needed: `α*` is only required to *select* an optimal allocation, and a
selection that jumps cannot be tracked.  This file supplies the continuity.

A selection of maximisers is not continuous in general — when the maximiser is
not unique the selection can jump between two of them arbitrarily.  Uniqueness at
the point of interest is exactly what rules this out, and it is all that is
needed: nothing is assumed about maximisers at nearby parameters, which may well
be non-unique.

## Statement

For `F : X → A → ℝ` jointly continuous along `univ ×ˢ S` and `S` compact, if
`a₀` is the *only*
maximiser of `F x₀` on `S`, then every maximiser of `F x` lies close to `a₀` once
`x` is close to `x₀`:

  `∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ a ∈ argmax_S (F x), dist a a₀ < ε`.

This is the argmax ("upper hemicontinuity") half of Berge's maximum theorem,
specialised to a singleton argmax, where it becomes an honest continuity
statement rather than a set-valued one.

## Proof

Contradiction plus compactness.  If the conclusion fails there are `x_n → x₀`
and maximisers `a_n` of `F x_n` staying `ε` away from `a₀`.  Compactness of `S`
extracts `a_{φ(n)} → a`, still `ε` away from `a₀`, hence `a ≠ a₀`.  Passing to
the limit in `F x_{φ(n)} a_{φ(n)} ≥ F x_{φ(n)} b` — legitimate because `F` is
jointly continuous and `b` is held fixed — shows `a` maximises `F x₀`.
Uniqueness gives `a = a₀`, the contradiction.

Joint continuity is what makes the limit step work: separate continuity in each
argument would not let `F x_{φ(n)} a_{φ(n)}` be compared with `F x₀ a`.  It is
only needed along `univ ×ˢ S`, since every point the argument evaluates `F` at
is feasible.
-/

open Filter Topology Metric

namespace BanditAlgorithm

variable {X A : Type*} [MetricSpace X] [MetricSpace A]

/-- `a` maximises `F x` over `S`. -/
def IsMaxOnSet (F : X → A → ℝ) (S : Set A) (x : X) (a : A) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, F x b ≤ F x a

/-! ## The main estimate -/

/-- **Maximisers near `x₀` are near the unique maximiser at `x₀`.**

Continuity of `F` is only required *along the feasible set* `univ ×ˢ S`.  This
matters for the intended application: the Track-and-Stop objective involves
`α_a α_b/(α_a + α_b)`, which is continuous on the closed simplex but genuinely
discontinuous off it, where the denominator can vanish with the numerator
nonzero. -/
theorem exists_delta_forall_isMaxOnSet_dist_lt {S : Set A} (hS : IsCompact S)
    {F : X → A → ℝ}
    (hF : ContinuousOn (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S))
    {x₀ : X} {a₀ : A}
    (huniq : ∀ a, IsMaxOnSet F S x₀ a → a = a₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : X, dist x x₀ < δ →
      ∀ a : A, IsMaxOnSet F S x a → dist a a₀ < ε := by
  by_contra hcon
  push_neg at hcon
  -- a counterexample at every scale `1/(n+1)`
  have hpick : ∀ n : ℕ, ∃ p : X × A,
      dist p.1 x₀ < 1 / ((n : ℝ) + 1) ∧ IsMaxOnSet F S p.1 p.2 ∧ ε ≤ dist p.2 a₀ := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨x, hx, a, hamax, hae⟩ := hcon (1 / ((n : ℝ) + 1)) hpos
    exact ⟨(x, a), hx, hamax, hae⟩
  choose q hq1 hq2 hq3 using hpick
  -- the parameters converge
  have hx : Tendsto (fun n ↦ (q n).1) atTop (𝓝 x₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hq1 n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- the maximisers subconverge
  obtain ⟨a, haS, φ, hφ, hlim⟩ := hS.tendsto_subseq (fun n ↦ (hq2 n).1)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- the limit is still `ε` away from `a₀`
  have hfar : ε ≤ dist a a₀ := by
    have hd : Tendsto (fun n ↦ dist (q (φ n)).2 a₀) atTop (𝓝 (dist a a₀)) :=
      hlim.dist tendsto_const_nhds
    exact ge_of_tendsto hd (Eventually.of_forall fun n ↦ hq3 (φ n))
  -- the limit maximises `F x₀`
  have hxsub : Tendsto (fun n ↦ (q (φ n)).1) atTop (𝓝 x₀) := hx.comp hφtop
  -- limits of `F` along sequences that stay in the feasible set
  have key : ∀ c ∈ S, ∀ z : ℕ → A, (∀ n, z n ∈ S) → Tendsto z atTop (𝓝 c) →
      Tendsto (fun n ↦ F (q (φ n)).1 (z n)) atTop (𝓝 (F x₀ c)) := by
    intro c hc z hz hzlim
    have hcw : ContinuousWithinAt (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S) (x₀, c) :=
      hF (x₀, c) ⟨Set.mem_univ _, hc⟩
    have hpair : Tendsto (fun n ↦ ((q (φ n)).1, z n)) atTop
        (𝓝[Set.univ ×ˢ S] (x₀, c)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hxsub.prodMk_nhds hzlim,
        Eventually.of_forall fun n ↦ ⟨Set.mem_univ _, hz n⟩⟩
    exact Filter.Tendsto.comp hcw hpair
  have hmax : IsMaxOnSet F S x₀ a := by
    refine ⟨haS, fun b hb ↦ ?_⟩
    have hleft : Tendsto (fun n ↦ F (q (φ n)).1 b) atTop (𝓝 (F x₀ b)) :=
      key b hb (fun _ ↦ b) (fun _ ↦ hb) tendsto_const_nhds
    have hright : Tendsto (fun n ↦ F (q (φ n)).1 (q (φ n)).2) atTop (𝓝 (F x₀ a)) :=
      key a haS (fun n ↦ (q (φ n)).2) (fun n ↦ (hq2 (φ n)).1) hlim
    refine le_of_tendsto_of_tendsto hleft hright ?_
    exact Eventually.of_forall fun n ↦ (hq2 (φ n)).2 b hb
  -- uniqueness closes the contradiction
  have : a = a₀ := huniq a hmax
  rw [this, dist_self] at hfar
  exact absurd hfar (not_le.mpr hε)

/-! ## Continuity of a selection

A *selection* is a function `sel : X → A` picking, for each parameter, some
maximiser.  The estimate above says any such selection is continuous at a point
of uniqueness — however it breaks ties elsewhere. -/

/-- **A selection of maximisers is continuous at every point where the maximiser
is unique.** -/
theorem continuousAt_of_isMaxOnSet {S : Set A} (hS : IsCompact S)
    {F : X → A → ℝ}
    (hF : ContinuousOn (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S))
    {x₀ : X} {sel : X → A}
    (hsel : ∀ x, IsMaxOnSet F S x (sel x))
    (huniq : ∀ a, IsMaxOnSet F S x₀ a → a = sel x₀) :
    ContinuousAt sel x₀ := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ :=
    exists_delta_forall_isMaxOnSet_dist_lt hS hF (a₀ := sel x₀) huniq hε
  rw [Metric.eventually_nhds_iff]
  exact ⟨δ, hδ, fun {x} hx ↦ hmain x hx (sel x) (hsel x)⟩

/-! ## Sequential form

The form the tracking argument consumes: parameters converging to `x₀` push any
choice of maximisers to the maximiser at `x₀`.  Note this does *not* require the
maximisers `a n` to be chosen by a single selection — an algorithm computing an
optimal allocation afresh at every round need not be consistent in its
tie-breaking. -/

/-- The eventual form: the maximiser property is only needed from some index on,
which is what a plug-in rule provides — early estimates need not even have a
maximiser of the right shape. -/
theorem tendsto_of_eventually_isMaxOnSet {S : Set A} (hS : IsCompact S)
    {F : X → A → ℝ}
    (hF : ContinuousOn (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S))
    {x₀ : X} {a₀ : A} (huniq : ∀ a, IsMaxOnSet F S x₀ a → a = a₀)
    {x : ℕ → X} (hx : Tendsto x atTop (𝓝 x₀))
    {a : ℕ → A} (ha : ∀ᶠ n in atTop, IsMaxOnSet F S (x n) (a n)) :
    Tendsto a atTop (𝓝 a₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := exists_delta_forall_isMaxOnSet_dist_lt hS hF huniq hε
  have hev : ∀ᶠ n in atTop, dist (x n) x₀ < δ := by
    rw [tendsto_iff_dist_tendsto_zero] at hx
    exact (hx.eventually (gt_mem_nhds hδ))
  filter_upwards [hev, ha] with n hn hna
  exact hmain (x n) hn (a n) hna

theorem tendsto_of_isMaxOnSet {S : Set A} (hS : IsCompact S)
    {F : X → A → ℝ}
    (hF : ContinuousOn (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S))
    {x₀ : X} {a₀ : A} (huniq : ∀ a, IsMaxOnSet F S x₀ a → a = a₀)
    {x : ℕ → X} (hx : Tendsto x atTop (𝓝 x₀))
    {a : ℕ → A} (ha : ∀ n, IsMaxOnSet F S (x n) (a n)) :
    Tendsto a atTop (𝓝 a₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := exists_delta_forall_isMaxOnSet_dist_lt hS hF huniq hε
  have hev : ∀ᶠ n in atTop, dist (x n) x₀ < δ := by
    rw [tendsto_iff_dist_tendsto_zero] at hx
    exact (hx.eventually (gt_mem_nhds hδ))
  filter_upwards [hev] with n hn
  exact hmain (x n) hn (a n) (ha n)

end BanditAlgorithm

/-!
# The optimal-allocation objective, and that it attains its maximum

Lattimore & Szepesvári Eq. (33.4) defines the best-arm-identification complexity
of a Gaussian bandit `ν` with unique best arm `i` as `c*(ν)⁻¹ = max_α Ψ_i(μ, α)`
over the probability simplex, where

  `Ψ_i(μ, α) = min_{j ≠ i} pairHarm (α_i) (α_j) · (μ_i − μ_j)²/2`.

The maximisers of `Ψ_i(μ, ·)` are the optimal allocations the sampling rule of
Track-and-Stop tracks.  This file establishes the two facts everything else
needs about `Ψ`:

* it is continuous on `ℝ^k ×ˢ Δ_{k−1}` (`continuousOn_alloRate`), so
* it attains its maximum on the simplex (`exists_isMaxOnSet_alloRate`).

Both are pure topology.  Continuity is where the corner value of `pairHarm`
matters: `Ψ` is a minimum of finitely many pair costs, each continuous on the
closed quadrant by `Solutions/HarmonicPair.lean`, and a minimum of finitely many
continuous functions is continuous.  Attainment is then compactness of the
simplex.

Attainment is not a formality.  `Ψ_i(μ, ·)` vanishes on the whole boundary face
`{α_i = 0}` and on each face `{α_j = 0}`, so the maximum is interior and a
supremum taken over the open simplex would not obviously be achieved; it is the
continuous extension to the closed simplex, corner value included, that makes
compactness applicable.

## What is *not* here

Uniqueness of the maximiser.  It is true for Gaussian best-arm identification
with a unique best arm, and `Solutions/ArgmaxContinuity.lean` shows it is exactly
what makes the optimal allocation depend continuously on `μ` — but it is a
separate (concavity) argument, and every statement below is stated so that
uniqueness enters as a hypothesis rather than being assumed silently.
-/

open Filter Topology Metric Finset

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The objective -/

/-- `Ψ_i(μ, α) = min_{j ≠ i} pairHarm (α_i) (α_j) (μ_i − μ_j)²/2`, the quantity
the optimal allocation maximises.  The nonemptiness proof is an argument because
the minimum is over `{j | j ≠ i}`, which is empty when `k = 1` — the degenerate
case where there is nothing to identify. -/
noncomputable def alloRate {i : Fin k} (hne : (Finset.univ.erase i).Nonempty)
    (μ α : Fin k → ℝ) : ℝ :=
  (Finset.univ.erase i).inf' hne fun j ↦ harmCost (α i) (α j) (μ i - μ j)

theorem mem_erase_iff_ne {i j : Fin k} : j ∈ Finset.univ.erase i ↔ j ≠ i := by
  simp

/-- The objective is at most each pair's cost. -/
theorem alloRate_le {i : Fin k} (hne : (Finset.univ.erase i).Nonempty)
    (μ α : Fin k → ℝ) {j : Fin k} (hj : j ≠ i) :
    alloRate hne μ α ≤ harmCost (α i) (α j) (μ i - μ j) :=
  Finset.inf'_le _ (mem_erase_iff_ne.mpr hj)

/-- …and it is the largest such bound. -/
theorem le_alloRate {i : Fin k} (hne : (Finset.univ.erase i).Nonempty)
    {μ α : Fin k → ℝ} {c : ℝ}
    (h : ∀ j, j ≠ i → c ≤ harmCost (α i) (α j) (μ i - μ j)) :
    c ≤ alloRate hne μ α :=
  Finset.le_inf' _ _ fun j hj ↦ h j (mem_erase_iff_ne.mp hj)

theorem alloRate_nonneg {i : Fin k} (hne : (Finset.univ.erase i).Nonempty)
    {μ α : Fin k → ℝ} (hα : ∀ j, 0 ≤ α j) : 0 ≤ alloRate hne μ α :=
  le_alloRate hne fun j _ ↦ harmCost_nonneg (hα i) (hα j) _

/-! ## The feasible set -/

/-- The probability simplex of allocations. -/
def alloSimplex (k : ℕ) : Set (Fin k → ℝ) := stdSimplex ℝ (Fin k)

theorem mem_alloSimplex {α : Fin k → ℝ} :
    α ∈ alloSimplex k ↔ (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1 := Iff.rfl

theorem isCompact_alloSimplex : IsCompact (alloSimplex k) :=
  isCompact_stdSimplex ℝ (Fin k)

theorem alloSimplex_nonempty [NeZero k] : (alloSimplex k).Nonempty := by
  refine ⟨fun _ ↦ ((k : ℝ))⁻¹, fun i ↦ ?_, ?_⟩
  · have : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
      exact_mod_cast this
    positivity
  · have hk : (k : ℝ) ≠ 0 := by
      have : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
      have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast this
      exact this.ne'
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

theorem nonneg_of_mem_alloSimplex {α : Fin k → ℝ} (hα : α ∈ alloSimplex k) (i : Fin k) :
    0 ≤ α i := hα.1 i

/-! ## Continuity

Each pair cost is continuous on the closed quadrant, and the objective is the
minimum of finitely many of them. -/

theorem continuousOn_harmCost_pair (i j : Fin k) :
    ContinuousOn (fun p : (Fin k → ℝ) × (Fin k → ℝ) ↦
        harmCost (p.2 i) (p.2 j) (p.1 i - p.1 j))
      (Set.univ ×ˢ alloSimplex k) := by
  have hmap : ContinuousOn
      (fun p : (Fin k → ℝ) × (Fin k → ℝ) ↦ ((p.2 i, p.2 j), p.1 i - p.1 j))
      (Set.univ ×ˢ alloSimplex k) := by
    fun_prop
  refine ContinuousOn.comp continuousOn_harmCost hmap ?_
  rintro ⟨μ, α⟩ ⟨-, hα⟩
  exact ⟨hα.1 i, hα.1 j⟩

/-- **The objective is continuous on `ℝ^k ×ˢ Δ`.** -/
theorem continuousOn_alloRate {i : Fin k} (hne : (Finset.univ.erase i).Nonempty) :
    ContinuousOn (fun p : (Fin k → ℝ) × (Fin k → ℝ) ↦ alloRate hne p.1 p.2)
      (Set.univ ×ˢ alloSimplex k) := by
  unfold alloRate
  exact ContinuousOn.finset_inf'_apply hne fun j _ ↦ continuousOn_harmCost_pair i j

/-! ## Attainment -/

/-- **An optimal allocation exists.**  The objective is continuous on the
compact simplex, so its maximum is attained. -/
theorem exists_isMaxOnSet_alloRate [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (μ : Fin k → ℝ) :
    ∃ α, IsMaxOnSet (fun m a ↦ alloRate hne m a) (alloSimplex k) μ α := by
  have hcont : ContinuousOn (fun a ↦ alloRate hne μ a) (alloSimplex k) := by
    unfold alloRate
    refine ContinuousOn.finset_inf'_apply hne fun j _ ↦ ?_
    have hmap : ContinuousOn (fun a : Fin k → ℝ ↦ ((a i, a j), μ i - μ j))
        (alloSimplex k) := by fun_prop
    refine ContinuousOn.comp continuousOn_harmCost hmap ?_
    intro a ha
    exact ⟨ha.1 i, ha.1 j⟩
  obtain ⟨α, hαS, hmax⟩ :=
    isCompact_alloSimplex.exists_isMaxOn (alloSimplex_nonempty (k := k)) hcont
  exact ⟨α, hαS, fun b hb ↦ hmax hb⟩

/-! ## The value is positive when the means separate the best arm

An allocation with all coordinates positive gives every pair a positive cost as
long as the corresponding mean gaps are nonzero, so the maximal value is
positive.  This is what makes `c*(ν)` finite, and it is where the assumption
"the best arm is strictly best" is used. -/

theorem alloRate_pos {i : Fin k} (hne : (Finset.univ.erase i).Nonempty)
    {μ α : Fin k → ℝ} (hα : ∀ j, 0 < α j) (hμ : ∀ j, j ≠ i → μ j ≠ μ i) :
    0 < alloRate hne μ α := by
  refine (Finset.lt_inf'_iff _).mpr fun j hj ↦ ?_
  have hjne : j ≠ i := mem_erase_iff_ne.mp hj
  have hgap : μ i - μ j ≠ 0 := sub_ne_zero.mpr (Ne.symm (hμ j hjne))
  unfold harmCost
  have hharm : 0 < pairHarm (α i) (α j) := pairHarm_pos (hα i) (hα j)
  have hsq : 0 < (μ i - μ j) ^ 2 := by positivity
  positivity

/-- Consequently the maximal value is positive: the uniform allocation already
witnesses it. -/
theorem exists_pos_alloRate [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) :
    ∃ α ∈ alloSimplex k, 0 < alloRate hne μ α := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine ⟨fun _ ↦ ((k : ℝ))⁻¹, ?_, alloRate_pos hne (fun _ ↦ by positivity) hμ⟩
  refine ⟨fun _ ↦ by positivity, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end BanditAlgorithm

/-!
# Strictness, superadditivity and the equality case for `pairHarm`

`Solutions/HarmonicPair.lean` collects the soft properties of `pairHarm x y =
xy/(x+y)`: nonnegativity, the bound by `min x y`, monotonicity, continuity on the
closed quadrant.  Uniqueness of the optimal allocation needs three sharper facts,
which are gathered here.

## 1. Strict monotonicity

`pairHarm x y < pairHarm x y'` for `0 < x` and `y < y'`.  Playing an arm more
*strictly* increases the evidence about every pair containing it, provided the
other arm of the pair is played at all.  This is what makes a maximiser of the
allocation objective equalise all its pair terms: an arm whose term is not
minimal can give up mass to those that are, strictly increasing the minimum.

## 2. A Lipschitz bound in the second argument

`pairHarm x y − pairHarm x (y − t) ≤ t` for `0 ≤ t ≤ y`.  The exact computation

  `pairHarm x y − pairHarm x (y−t) = t x²/((x+y)(x+y−t))`

shows the drop is at most `t`, since `x² ≤ (x+y)(x+y−t)`.  This is what makes
the perturbation argument quantitative: it names how small a transfer has to be
for the donating arm to stay above the old minimum, with no appeal to continuity
or to a compactness argument for the size of the step.

## 3. Superadditivity, with its equality case

  `pairHarm x₁ y₁ + pairHarm x₂ y₂ ≤ pairHarm (x₁+x₂) (y₁+y₂)`,

with equality **iff** `x₁ y₂ = x₂ y₁`, i.e. iff the two points lie on a common
ray through the origin.  Clearing denominators turns the difference into exactly
`(x₁y₂ − x₂y₁)²`, so both the inequality and its equality case come from a single
algebraic identity:

  `(x₁+x₂)(y₁+y₂)(x₁+y₁)(x₂+y₂) − [x₁y₁(x₂+y₂) + x₂y₂(x₁+y₁)](x₁+x₂+y₁+y₂)
     = (x₁y₂ − x₂y₁)²`.

Since `pairHarm` is positively homogeneous of degree one, superadditivity *is*
concavity, and the equality case says the concavity is strict in every direction
except along rays — which is the strongest form available, because homogeneity
makes `pairHarm` genuinely linear along each ray.  That is exactly the dichotomy
the uniqueness proof exploits: two distinct maximisers would have to be
proportional pair by pair, and two proportional points of the simplex are equal.
-/

namespace BanditAlgorithm

/-! ## Strict monotonicity -/

/-- **`pairHarm` is strictly increasing in its second argument** when the first
is positive. -/
theorem pairHarm_lt_of_lt_right {x y y' : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyy : y < y') :
    pairHarm x y < pairHarm x y' := by
  have hy' : 0 < y' := lt_of_le_of_lt hy hyy
  unfold pairHarm
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (mul_pos hx hx) (sub_pos.mpr hyy)]

/-- The combined strict bound: increasing the second argument strictly, and the
first weakly, strictly increases the value. -/
theorem pairHarm_lt_of_le_of_lt {x x' y y' : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hxx : x ≤ x') (hyy : y < y') : pairHarm x y < pairHarm x' y' := by
  have hy' : 0 < y' := lt_of_le_of_lt hy hyy
  have hx' : 0 < x' := lt_of_lt_of_le hx hxx
  calc pairHarm x y < pairHarm x y' := pairHarm_lt_of_lt_right hx hy hyy
    _ ≤ pairHarm x' y' := pairHarm_mono hx hy' hxx le_rfl

/-! ## The Lipschitz bound -/

/-- **Reducing the second argument by `t` costs at most `t`.**  The exact drop is
`t x²/((x+y)(x+y−t))`, and `x² ≤ (x+y)(x+y−t)` whenever `t ≤ y`. -/
theorem pairHarm_sub_le {x y t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) (hty : t ≤ y) :
    pairHarm x y - t ≤ pairHarm x (y - t) := by
  have hy : 0 ≤ y := le_trans ht hty
  have hd1 : (0 : ℝ) < x + y := by linarith
  have hd2 : (0 : ℝ) < x + (y - t) := by linarith
  unfold pairHarm
  rw [sub_le_iff_le_add, div_add' _ _ _ hd2.ne', div_le_div_iff₀ hd1 hd2]
  -- the difference is `t x² ≥ 0` after clearing denominators
  nlinarith [mul_nonneg ht (sq_nonneg x), mul_nonneg (mul_nonneg ht hy) hy,
    mul_nonneg (mul_nonneg ht hx.le) hy]

/-! ## Homogeneity -/

/-- `pairHarm` is positively homogeneous of degree one. -/
theorem pairHarm_smul {c x y : ℝ} (hc : 0 ≤ c) :
    pairHarm (c * x) (c * y) = c * pairHarm x y := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · simp [← hc0]
  · unfold pairHarm
    rw [← mul_add]
    field_simp

/-! ## Superadditivity and its equality case -/

/-- The algebraic identity behind both the inequality and its equality case. -/
theorem pairHarm_add_key (x₁ y₁ x₂ y₂ : ℝ) :
    (x₁ + x₂) * (y₁ + y₂) * ((x₁ + y₁) * (x₂ + y₂))
        - (x₁ * y₁ * (x₂ + y₂) + x₂ * y₂ * (x₁ + y₁)) * ((x₁ + x₂) + (y₁ + y₂))
      = (x₁ * y₂ - x₂ * y₁) ^ 2 := by
  ring

/-- **Superadditivity.**  Merging two pairs is at least as informative as the
two separately. -/
theorem pairHarm_add_le {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁) (hy₁ : 0 < y₁)
    (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) :
    pairHarm x₁ y₁ + pairHarm x₂ y₂ ≤ pairHarm (x₁ + x₂) (y₁ + y₂) := by
  have hd1 : (0 : ℝ) < x₁ + y₁ := by linarith
  have hd2 : (0 : ℝ) < x₂ + y₂ := by linarith
  have hd : (0 : ℝ) < (x₁ + x₂) + (y₁ + y₂) := by linarith
  unfold pairHarm
  rw [div_add_div _ _ hd1.ne' hd2.ne', div_le_div_iff₀ (by positivity) hd]
  nlinarith [sq_nonneg (x₁ * y₂ - x₂ * y₁), pairHarm_add_key x₁ y₁ x₂ y₂]

/-- **The equality case.**  Superadditivity is strict unless the two points are
proportional. -/
theorem pairHarm_add_eq_iff {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁) (hy₁ : 0 < y₁)
    (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) :
    pairHarm x₁ y₁ + pairHarm x₂ y₂ = pairHarm (x₁ + x₂) (y₁ + y₂)
      ↔ x₁ * y₂ = x₂ * y₁ := by
  have hd1 : (0 : ℝ) < x₁ + y₁ := by linarith
  have hd2 : (0 : ℝ) < x₂ + y₂ := by linarith
  have hd : (0 : ℝ) < (x₁ + x₂) + (y₁ + y₂) := by linarith
  constructor
  · intro heq
    -- clearing denominators, the difference is `(x₁y₂ − x₂y₁)²`
    have hclear : (x₁ * y₁ * (x₂ + y₂) + x₂ * y₂ * (x₁ + y₁)) * ((x₁ + x₂) + (y₁ + y₂))
        = (x₁ + x₂) * (y₁ + y₂) * ((x₁ + y₁) * (x₂ + y₂)) := by
      unfold pairHarm at heq
      rw [div_add_div _ _ hd1.ne' hd2.ne', div_eq_div_iff (by positivity) hd.ne'] at heq
      linarith [heq]
    have hsq : (x₁ * y₂ - x₂ * y₁) ^ 2 = 0 := by
      rw [← pairHarm_add_key x₁ y₁ x₂ y₂]
      linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith
  · intro hprop
    have hclear : (x₁ * y₁ * (x₂ + y₂) + x₂ * y₂ * (x₁ + y₁)) * ((x₁ + x₂) + (y₁ + y₂))
        = (x₁ + x₂) * (y₁ + y₂) * ((x₁ + y₁) * (x₂ + y₂)) := by
      have := pairHarm_add_key x₁ y₁ x₂ y₂
      have hz : (x₁ * y₂ - x₂ * y₁) ^ 2 = 0 := by
        rw [hprop]; ring
      linarith
    unfold pairHarm
    rw [div_add_div _ _ hd1.ne' hd2.ne', div_eq_div_iff (by positivity) hd.ne']
    linarith

/-! ## The midpoint form

The form used by the uniqueness argument: the value at the midpoint of two
points dominates the average of the values, strictly unless the two points are
proportional. -/

theorem pairHarm_midpoint_le {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁) (hy₁ : 0 < y₁)
    (hx₂ : 0 < x₂) (hy₂ : 0 < y₂) :
    (pairHarm x₁ y₁ + pairHarm x₂ y₂) / 2
      ≤ pairHarm ((x₁ + x₂) / 2) ((y₁ + y₂) / 2) := by
  have hhalf : pairHarm ((x₁ + x₂) / 2) ((y₁ + y₂) / 2)
      = pairHarm (x₁ + x₂) (y₁ + y₂) / 2 := by
    have := pairHarm_smul (c := (1 : ℝ) / 2) (x := x₁ + x₂) (y := y₁ + y₂) (by norm_num)
    rw [show ((x₁ + x₂) / 2 : ℝ) = 1 / 2 * (x₁ + x₂) by ring,
      show ((y₁ + y₂) / 2 : ℝ) = 1 / 2 * (y₁ + y₂) by ring, this]
    ring
  rw [hhalf]
  have := pairHarm_add_le hx₁ hy₁ hx₂ hy₂
  linarith

/-- Equality at the midpoint forces proportionality. -/
theorem proportional_of_pairHarm_midpoint_eq {x₁ y₁ x₂ y₂ : ℝ} (hx₁ : 0 < x₁)
    (hy₁ : 0 < y₁) (hx₂ : 0 < x₂) (hy₂ : 0 < y₂)
    (heq : pairHarm ((x₁ + x₂) / 2) ((y₁ + y₂) / 2)
      ≤ (pairHarm x₁ y₁ + pairHarm x₂ y₂) / 2) :
    x₁ * y₂ = x₂ * y₁ := by
  have hhalf : pairHarm ((x₁ + x₂) / 2) ((y₁ + y₂) / 2)
      = pairHarm (x₁ + x₂) (y₁ + y₂) / 2 := by
    have := pairHarm_smul (c := (1 : ℝ) / 2) (x := x₁ + x₂) (y := y₁ + y₂) (by norm_num)
    rw [show ((x₁ + x₂) / 2 : ℝ) = 1 / 2 * (x₁ + x₂) by ring,
      show ((y₁ + y₂) / 2 : ℝ) = 1 / 2 * (y₁ + y₂) by ring, this]
    ring
  rw [hhalf] at heq
  have hle := pairHarm_add_le hx₁ hy₁ hx₂ hy₂
  have : pairHarm x₁ y₁ + pairHarm x₂ y₂ = pairHarm (x₁ + x₂) (y₁ + y₂) := by linarith
  exact (pairHarm_add_eq_iff hx₁ hy₁ hx₂ hy₂).mp this

end BanditAlgorithm

/-!
# The optimal allocation is unique

`Solutions/AllocationObjective.lean` shows the objective

  `Ψ_i(μ, α) = min_{j ≠ i} pairHarm (α_i) (α_j) · (μ_i − μ_j)²/2`

attains its maximum on the simplex.  This file shows the maximiser is **unique**
whenever arm `i` is strictly best — Garivier & Kaufmann's Lemma 4.  That is what
makes "the optimal allocation `α*(μ)`" a well-defined function of `μ` rather than
a choice, and by `Solutions/ArgmaxContinuity.lean` it is also exactly what makes
that function continuous, hence trackable.

## Three steps

**Full support.**  The maximal value is positive (the uniform allocation already
achieves a positive value), and a pair term vanishes as soon as either of its two
coordinates does.  So every maximiser has all coordinates strictly positive.
This is where `μ_j ≠ μ_i` enters.

**Equalisation.**  At a maximiser *every* pair term equals the value
(`alloRate_eq_harmCost_of_isOptimal`).  If some arm `j₀`'s term were strictly
larger, transfer a small amount `t` of mass from `j₀` to every other arm.  Each
other term strictly increases (`pairHarm_lt_of_le_of_lt`), while `j₀`'s term
drops by at most `t·(μ_i − μ_{j₀})²/2` (`pairHarm_sub_le`); choosing
`t ≤ (term_{j₀} − value)/(μ_i − μ_{j₀})²` keeps it above the value too, so the
minimum strictly increases — contradicting maximality.  The Lipschitz bound is
what makes this a finite computation rather than a continuity argument, and the
transfer is capped at `α_{j₀}/2` so that the donating arm is never emptied.

**Uniqueness.**  Given two maximisers `α`, `β`, their midpoint `γ` is feasible
and, by superadditivity of `pairHarm`, every term of `γ` is at least the average
of the corresponding terms of `α` and `β` — hence at least the value.  So `γ` is
a maximiser too, and by equalisation *every* term of `γ` equals the value.  That
forces equality in superadditivity for every `j`, and the equality case
(`proportional_of_pairHarm_midpoint_eq`) gives `α_i β_j = β_i α_j` for all `j`.
So `β = (β_i/α_i)·α`, and two proportional probability vectors are equal.

The reason the argument needs equalisation, and not merely concavity, is that
`Ψ` is a *minimum*: knowing `Ψ(γ) = Ψ(α) = Ψ(β)` by itself only pins down the
terms that are active at `γ`, and proportionality on one pair says nothing about
the others.  Equalisation makes every pair active at once.
-/

open Filter Topology Finset

namespace BanditAlgorithm

variable {k : ℕ}

/-- `α` is an optimal allocation for the means `μ` with best arm `i`. -/
def IsOptimalAllo {i : Fin k} (hne : (Finset.univ.erase i).Nonempty)
    (μ α : Fin k → ℝ) : Prop :=
  IsMaxOnSet (fun m a ↦ alloRate hne m a) (alloSimplex k) μ α

theorem two_le_of_erase_nonempty {i : Fin k} (hne : (Finset.univ.erase i).Nonempty) :
    2 ≤ k := by
  obtain ⟨j, hj⟩ := hne
  have hji : j ≠ i := mem_erase_iff_ne.mp hj
  by_contra hk
  push_neg at hk
  interval_cases k
  · exact absurd j.isLt (by omega)
  · exact hji (Subsingleton.elim j i)

/-! ## The value is positive, and maximisers have full support -/

theorem pos_alloRate_of_isOptimal [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ α : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) (hopt : IsOptimalAllo hne μ α) :
    0 < alloRate hne μ α := by
  obtain ⟨α₀, hα₀S, hα₀pos⟩ := exists_pos_alloRate hne hμ
  exact lt_of_lt_of_le hα₀pos (hopt.2 α₀ hα₀S)

/-- **Every optimal allocation has full support.**  A pair term vanishes when
either of its coordinates does, so an allocation starving an arm has value `0`
and cannot be optimal. -/
theorem pos_of_isOptimal [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ α : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) (hopt : IsOptimalAllo hne μ α) (j : Fin k) :
    0 < α j := by
  have hV := pos_alloRate_of_isOptimal hne hμ hopt
  have hnn : ∀ l, 0 ≤ α l := hopt.1.1
  obtain ⟨j₁, hj₁⟩ := id hne
  have hj₁i : j₁ ≠ i := mem_erase_iff_ne.mp hj₁
  rcases eq_or_lt_of_le (hnn j) with hzero | hlt
  · exfalso
    by_cases hji : j = i
    · have hle := alloRate_le hne μ α hj₁i
      unfold harmCost at hle
      rw [show α i = 0 by rw [← hji, ← hzero], pairHarm_zero_left] at hle
      simp only [zero_mul, zero_div] at hle
      linarith
    · have hle := alloRate_le hne μ α hji
      unfold harmCost at hle
      rw [show α j = 0 from hzero.symm, pairHarm_zero_right] at hle
      simp only [zero_mul, zero_div] at hle
      linarith
  · exact hlt

/-! ## Equalisation -/

/-- Distributing `c₂` to every arm but `j₀`, which gets `c₁`. -/
theorem sum_ite_const {j₀ : Fin k} (hk : 1 ≤ k) (c₁ c₂ : ℝ) :
    ∑ j : Fin k, (if j = j₀ then c₁ else c₂) = c₁ + ((k : ℝ) - 1) * c₂ := by
  classical
  rw [← Finset.add_sum_erase Finset.univ (fun j ↦ if j = j₀ then c₁ else c₂)
    (Finset.mem_univ j₀)]
  simp only [if_pos rfl]
  congr 1
  rw [Finset.sum_congr rfl (fun j hj ↦ if_neg (Finset.ne_of_mem_erase hj)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j₀),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  push_cast [Nat.cast_sub hk]
  ring

/-- **At an optimal allocation every pair term equals the value.**  Otherwise a
small transfer of mass away from a strictly-better-than-minimal arm raises the
minimum. -/
theorem alloRate_eq_harmCost_of_isOptimal [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ α : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) (hopt : IsOptimalAllo hne μ α)
    {j₀ : Fin k} (hj₀ : j₀ ≠ i) :
    harmCost (α i) (α j₀) (μ i - μ j₀) = alloRate hne μ α := by
  classical
  have hk2 : 2 ≤ k := two_le_of_erase_nonempty hne
  have hkpos : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hpos : ∀ j, 0 < α j := pos_of_isOptimal hne hμ hopt
  have hVpos : 0 < alloRate hne μ α := pos_alloRate_of_isOptimal hne hμ hopt
  refine le_antisymm ?_ (alloRate_le hne μ α hj₀)
  by_contra hcon
  push_neg at hcon
  -- the excess at `j₀`, and the squared gap
  have hg₀ : (0 : ℝ) < (μ i - μ j₀) ^ 2 := by
    have : μ i - μ j₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm (hμ j₀ hj₀))
    positivity
  have hε₀ : 0 < harmCost (α i) (α j₀) (μ i - μ j₀) - alloRate hne μ α := by linarith
  -- the transfer: small enough to keep `j₀` above the value, and to not empty it
  set t : ℝ := min (α j₀ / 2)
    ((harmCost (α i) (α j₀) (μ i - μ j₀) - alloRate hne μ α) / (μ i - μ j₀) ^ 2)
    with htdef
  have ht0 : 0 < t := lt_min (by linarith [hpos j₀]) (by positivity)
  have hthalf : t ≤ α j₀ / 2 := min_le_left _ _
  have htj : t ≤ α j₀ := le_trans hthalf (by linarith [hpos j₀])
  have htg : t * (μ i - μ j₀) ^ 2
      ≤ harmCost (α i) (α j₀) (μ i - μ j₀) - alloRate hne μ α := by
    have h := min_le_right (α j₀ / 2)
      ((harmCost (α i) (α j₀) (μ i - μ j₀) - alloRate hne μ α) / (μ i - μ j₀) ^ 2)
    rw [← htdef] at h
    rw [← le_div_iff₀ hg₀]
    exact h
  -- the perturbed allocation
  set β : Fin k → ℝ :=
    fun j ↦ α j + (if j = j₀ then -t else t / ((k : ℝ) - 1)) with hβdef
  have hstep : (0 : ℝ) < t / ((k : ℝ) - 1) := by positivity
  have hβi : β i = α i + t / ((k : ℝ) - 1) := by
    simp only [hβdef, if_neg (fun h : i = j₀ ↦ hj₀ h.symm)]
  have hβj₀ : β j₀ = α j₀ - t := by
    have hb : β j₀ = α j₀ + (if (j₀ : Fin k) = j₀ then -t else t / ((k : ℝ) - 1)) := by
      rw [hβdef]
    rw [hb, if_pos rfl]; ring
  have hβother : ∀ j, j ≠ j₀ → β j = α j + t / ((k : ℝ) - 1) := by
    intro j hj; simp only [hβdef, if_neg hj]
  have hβi_ge : α i ≤ β i := by rw [hβi]; linarith
  -- feasibility
  have hβsimplex : β ∈ alloSimplex k := by
    refine ⟨fun j ↦ ?_, ?_⟩
    · by_cases hj : j = j₀
      · rw [hj, hβj₀]; linarith [hpos j₀]
      · rw [hβother j hj]; linarith [(hpos j).le]
    · have hb : ∀ j : Fin k, β j = α j + (if j = j₀ then -t else t / ((k : ℝ) - 1)) := by
        intro j; rw [hβdef]
      rw [Finset.sum_congr rfl (fun j _ ↦ hb j), Finset.sum_add_distrib, hopt.1.2,
        sum_ite_const (by omega) (-t) (t / ((k : ℝ) - 1))]
      field_simp
      ring
  -- every pair term of `β` is strictly above the value
  have hbetter : ∀ j, j ≠ i → alloRate hne μ α < harmCost (β i) (β j) (μ i - μ j) := by
    intro j hj
    have hgj : (0 : ℝ) < (μ i - μ j) ^ 2 := by
      have : μ i - μ j ≠ 0 := sub_ne_zero.mpr (Ne.symm (hμ j hj))
      positivity
    by_cases hjj₀ : j = j₀
    · -- the donating arm loses at most `t·gap²/2`, which the excess covers
      rw [hjj₀]
      have hj₀pos : 0 < α j₀ - t := by linarith [hpos j₀]
      have hs1 : pairHarm (α i) (α j₀) - t ≤ pairHarm (α i) (α j₀ - t) :=
        pairHarm_sub_le (hpos i) ht0.le htj
      have hs2 : pairHarm (α i) (α j₀ - t) ≤ pairHarm (β i) (β j₀) := by
        rw [hβj₀]
        exact pairHarm_mono (hpos i) hj₀pos hβi_ge le_rfl
      have hharm : pairHarm (α i) (α j₀) - t ≤ pairHarm (β i) (β j₀) := le_trans hs1 hs2
      unfold harmCost at htg hε₀ ⊢
      nlinarith [hharm, hg₀, htg, hε₀]
    · -- every other arm strictly gains
      have hlt : pairHarm (α i) (α j) < pairHarm (β i) (β j) := by
        rw [hβother j hjj₀]
        exact pairHarm_lt_of_le_of_lt (hpos i) (hpos j).le hβi_ge (by linarith)
      have hold := alloRate_le hne μ α hj
      unfold harmCost at hold ⊢
      nlinarith [hlt, hgj]
  -- contradiction with maximality
  have hgt : alloRate hne μ α < alloRate hne μ β :=
    (Finset.lt_inf'_iff _).mpr fun j hj ↦ hbetter j (mem_erase_iff_ne.mp hj)
  exact absurd (hopt.2 β hβsimplex) (not_le.mpr hgt)

/-! ## Uniqueness -/

/-- **The optimal allocation is unique.**  Garivier & Kaufmann, Lemma 4. -/
theorem eq_of_isOptimal [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ α β : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i)
    (hα : IsOptimalAllo hne μ α) (hβ : IsOptimalAllo hne μ β) : α = β := by
  classical
  have hαpos : ∀ j, 0 < α j := pos_of_isOptimal hne hμ hα
  have hβpos : ∀ j, 0 < β j := pos_of_isOptimal hne hμ hβ
  -- both maximisers have the same value
  have hval : alloRate hne μ β = alloRate hne μ α :=
    le_antisymm (hα.2 β hβ.1) (hβ.2 α hα.1)
  -- the midpoint is feasible
  set γ : Fin k → ℝ := fun j ↦ (α j + β j) / 2 with hγdef
  have hγpos : ∀ j, 0 < γ j := fun j ↦ by
    simp only [hγdef]; linarith [hαpos j, hβpos j]
  have hγS : γ ∈ alloSimplex k := by
    refine ⟨fun j ↦ (hγpos j).le, ?_⟩
    have : ∑ j : Fin k, γ j = ((∑ j : Fin k, α j) + ∑ j : Fin k, β j) / 2 := by
      simp only [hγdef]
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]
    rw [this, hα.1.2, hβ.1.2]
    norm_num
  -- every term of the midpoint is at least the common value
  have hterm : ∀ j, j ≠ i →
      alloRate hne μ α ≤ harmCost (γ i) (γ j) (μ i - μ j) := by
    intro j hj
    have hmid : (pairHarm (α i) (α j) + pairHarm (β i) (β j)) / 2
        ≤ pairHarm (γ i) (γ j) :=
      pairHarm_midpoint_le (hαpos i) (hαpos j) (hβpos i) (hβpos j)
    have hgj : (0 : ℝ) ≤ (μ i - μ j) ^ 2 := sq_nonneg _
    have hEα := alloRate_eq_harmCost_of_isOptimal hne hμ hα hj
    have hEβ := alloRate_eq_harmCost_of_isOptimal hne hμ hβ hj
    rw [hval] at hEβ
    unfold harmCost at hEα hEβ ⊢
    nlinarith [hmid, hgj]
  -- so the midpoint is optimal too
  have hγval : alloRate hne μ γ = alloRate hne μ α := by
    refine le_antisymm (hα.2 γ hγS) ?_
    exact le_alloRate hne fun j hj ↦ hterm j hj
  have hγopt : IsOptimalAllo hne μ γ :=
    ⟨hγS, fun b hb ↦ le_trans (hα.2 b hb) (le_of_eq hγval.symm)⟩
  -- equalisation at the midpoint forces proportionality on every pair
  have hprop : ∀ j, j ≠ i → α i * β j = β i * α j := by
    intro j hj
    have hgj : (0 : ℝ) < (μ i - μ j) ^ 2 := by
      have : μ i - μ j ≠ 0 := sub_ne_zero.mpr (Ne.symm (hμ j hj))
      positivity
    have hEγ := alloRate_eq_harmCost_of_isOptimal hne hμ hγopt hj
    rw [hγval] at hEγ
    have hEα := alloRate_eq_harmCost_of_isOptimal hne hμ hα hj
    have hEβ := alloRate_eq_harmCost_of_isOptimal hne hμ hβ hj
    rw [hval] at hEβ
    -- the midpoint value equals the average, so superadditivity is tight
    have hharm : pairHarm (γ i) (γ j)
        ≤ (pairHarm (α i) (α j) + pairHarm (β i) (β j)) / 2 := by
      unfold harmCost at hEγ hEα hEβ
      nlinarith [hgj]
    refine proportional_of_pairHarm_midpoint_eq (hαpos i) (hαpos j) (hβpos i)
      (hβpos j) ?_
    simpa only [hγdef] using hharm
  -- a proportional pair of probability vectors is a single vector
  set r : ℝ := β i / α i with hrdef
  have hαi : (α i) ≠ 0 := (hαpos i).ne'
  have hall : ∀ j, β j = r * α j := by
    intro j
    by_cases hj : j = i
    · rw [hj, hrdef]
      field_simp
    · have h := hprop j hj
      rw [hrdef]
      field_simp
      linear_combination h
  have hsum : (1 : ℝ) = r := by
    have h1 : ∑ j : Fin k, β j = r * ∑ j : Fin k, α j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ hall j
    rw [hα.1.2, hβ.1.2, mul_one] at h1
    exact h1
  funext j
  have := hall j
  rw [← hsum, one_mul] at this
  exact this.symm

end BanditAlgorithm

/-!
# The optimal allocation depends continuously on the means

This is the join of the two previous files.  `Solutions/AllocationUnique.lean`
shows the maximiser of `Ψ_i(μ, ·)` is unique when arm `i` is strictly best;
`Solutions/ArgmaxContinuity.lean` shows a selection of maximisers is continuous
at every point of uniqueness.  Together: the optimal allocation `α*(·)` is
continuous at every `μ` with a strictly best arm, no matter how it breaks ties
elsewhere.

That is precisely the hypothesis `hcont` of
`TrackingCesaro.tendsto_targets_of_continuousAt`, and it closes the circularity
the Track-and-Stop analysis has to get past: the rule tracks `α*(μ̂(s))`, whose
convergence to `α*(μ)` cannot be read off from `μ̂(s) → μ` unless `α*` is
continuous, and `α*` is a selection from an argmax, which in general is not.

## The best arm is locally constant

One more ingredient is needed before this can be applied to a real sampling
rule.  `Ψ_i` is indexed by a *fixed* candidate best arm `i`, but the rule
plugs in the empirical best arm `î(s)`, which is a discontinuous function of the
estimates.  The saving grace is `eventually_strictly_best`: having a strictly
best arm is an open condition — finitely many strict inequalities — so near a `μ`
whose best arm is `i`, every `m` also has `i` strictly best.  Along a sequence
`μ̂(s) → μ` the plug-in index is therefore *eventually equal to* `i`, and from
that round on the rule is tracking the fixed-index objective this file controls.

Nothing here needs the best arm to be identified correctly early: only that it
is correct eventually, which is all a Cesàro limit sees.
-/

open Filter Topology Metric Finset

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## A canonical optimal allocation -/

/-- A choice of optimal allocation for every parameter vector, obtained from
compactness.  For parameters with a strictly best arm it is *the* optimal
allocation, by `eq_of_isOptimal`; elsewhere it is an arbitrary maximiser. -/
noncomputable def optimalAllocation [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (μ : Fin k → ℝ) : Fin k → ℝ :=
  (exists_isMaxOnSet_alloRate hne μ).choose

theorem optimalAllocation_spec [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (μ : Fin k → ℝ) :
    IsOptimalAllo hne μ (optimalAllocation hne μ) :=
  (exists_isMaxOnSet_alloRate hne μ).choose_spec

theorem optimalAllocation_mem [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (μ : Fin k → ℝ) :
    optimalAllocation hne μ ∈ alloSimplex k :=
  (optimalAllocation_spec hne μ).1

/-- Any optimal allocation at a parameter with a strictly best arm *is* the
canonical one. -/
theorem eq_optimalAllocation [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ α : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) (hα : IsOptimalAllo hne μ α) :
    α = optimalAllocation hne μ :=
  eq_of_isOptimal hne hμ hα (optimalAllocation_spec hne μ)

/-! ## Continuity -/

/-- **Any selection of optimal allocations is continuous where the best arm is
strict.** -/
theorem continuousAt_of_isOptimalAllo [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty)
    {sel : (Fin k → ℝ) → (Fin k → ℝ)} (hsel : ∀ m, IsOptimalAllo hne m (sel m))
    {μ : Fin k → ℝ} (hμ : ∀ j, j ≠ i → μ j ≠ μ i) :
    ContinuousAt sel μ := by
  refine continuousAt_of_isMaxOnSet isCompact_alloSimplex (continuousOn_alloRate hne)
    (fun x ↦ hsel x) ?_
  intro a ha
  exact eq_of_isOptimal hne hμ ha (hsel μ)

/-- The canonical optimal allocation is continuous where the best arm is
strict. -/
theorem continuousAt_optimalAllocation [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) :
    ContinuousAt (optimalAllocation hne) μ :=
  continuousAt_of_isOptimalAllo hne (optimalAllocation_spec hne) hμ

/-- **The sequential form used by the tracking argument.**  Estimates converging
to a parameter with a strictly best arm push *any* optimal allocations computed
from them to the optimal allocation at the limit — with no assumption that the
computation is consistent from round to round. -/
theorem tendsto_optimal_of_tendsto [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) {a : ℕ → Fin k → ℝ}
    (ha : ∀ s, IsOptimalAllo hne (m s) (a s)) :
    Tendsto a atTop (𝓝 (optimalAllocation hne μ)) := by
  refine tendsto_of_isMaxOnSet isCompact_alloSimplex (continuousOn_alloRate hne)
    (a₀ := optimalAllocation hne μ) ?_ hm ha
  intro b hb
  exact eq_of_isOptimal hne hμ hb (optimalAllocation_spec hne μ)

/-- Coordinatewise, which is the form the Cesàro lemma consumes. -/
theorem tendsto_optimal_coord [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) {a : ℕ → Fin k → ℝ}
    (ha : ∀ s, IsOptimalAllo hne (m s) (a s)) (j : Fin k) :
    Tendsto (fun s ↦ a s j) atTop (𝓝 (optimalAllocation hne μ j)) :=
  ((continuous_apply j).continuousAt.tendsto).comp
    (tendsto_optimal_of_tendsto hne hμ hm ha)

/-! ## Having a strictly best arm is an open condition -/

/-- **A strictly best arm stays strictly best under small perturbations.**
Finitely many strict inequalities define an open set. -/
theorem eventually_strictly_best {i : Fin k} {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j < μ i) :
    ∀ᶠ m in 𝓝 μ, ∀ j, j ≠ i → m j < m i := by
  have hcoord : ∀ j : Fin k, j ≠ i → ∀ᶠ m in 𝓝 μ, m j < m i := by
    intro j hj
    have hcont : ContinuousAt (fun m : Fin k → ℝ ↦ m i - m j) μ := by fun_prop
    have hpos : 0 < μ i - μ j := by linarith [hμ j hj]
    have := hcont.tendsto.eventually (lt_mem_nhds hpos)
    filter_upwards [this] with m hm
    linarith
  have hall : ∀ᶠ m in 𝓝 μ, ∀ j ∈ Finset.univ.erase i, m j < m i := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact hcoord j (mem_erase_iff_ne.mp hj)
  filter_upwards [hall] with m hm j hj
  exact hm j (mem_erase_iff_ne.mpr hj)

/-- The sequential form: along estimates converging to a parameter with a
strictly best arm, the plug-in best arm is eventually the true one. -/
theorem eventually_strictly_best_seq {i : Fin k} {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j < μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) :
    ∀ᶠ s in atTop, ∀ j, j ≠ i → m s j < m s i :=
  hm.eventually (eventually_strictly_best hμ)

end BanditAlgorithm

/-!
# The D-Tracking sampling rule, and its deterministic guarantee

Everything the Track-and-Stop sampling rule needs is now available, so this file
builds the rule and proves what it achieves.  The rule is:

  at round `t`, play an arm maximising `∑_{s<t} p_j(s) − N_j(t)`,
  where `p(s) = (1 − kε_s)·α*(μ̂(s)) + ε_s·𝟙` and `ε_s = 1/(2√(k²+s))`.

That is one line, and it does both jobs: forced exploration is not a separate
branch but a consequence of the floor `ε_s` inside the target.

## What is proved

For *any* sequence of estimates `m(0), m(1), …` converging to a parameter `μ`
with a strictly best arm — in the application, the empirical means, which
converge because the same rule guarantees every arm is sampled — the counts
produced by the rule satisfy

* `√(k² + t) − 2k + 1 ≤ N_j(t)` for every arm and every round
  (`sqrt_le_trackCounts`), and
* `N_j(t)/t → α*_j(μ)` (`tendsto_trackCounts_div`).

The first is Garivier & Kaufmann's Lemma 7, the second their Lemma 8 combined
with Proposition 9.  Both are deterministic: no probability appears, because the
estimates enter only through their convergence.  The probabilistic content of
Track-and-Stop — that the empirical means do converge — is separate, and is what
`Solutions/MeanDeviation.lean` and `Solutions/MeanSettling.lean` supply.

## The circularity, and where it is broken

The rule computes its targets from the estimates, and the estimates are only
accurate because the rule samples every arm.  The order of reasoning that avoids
circularity is: the floor `ε_s` gives the count bound *unconditionally*
(`Solutions/TrackingForced.lean`, no hypothesis on the targets at all); the count
bound gives convergence of the estimates; convergence of the estimates gives
convergence of the targets (`Solutions/AllocationContinuity.lean`, where
uniqueness of `α*` is what makes this step legal); and convergence of the targets
gives convergence of the allocation, by Cesàro.  Each step depends only on the
previous one.
-/

open Filter Topology Finset

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## Choosing a maximal coordinate -/

/-- An arm maximising `f`, ties broken arbitrarily. -/
noncomputable def argMaxArm [NeZero k] (f : Fin k → ℝ) : Fin k :=
  (Finset.exists_max_image Finset.univ f Finset.univ_nonempty).choose

theorem le_argMaxArm [NeZero k] (f : Fin k → ℝ) (j : Fin k) :
    f j ≤ f (argMaxArm f) :=
  (Finset.exists_max_image Finset.univ f Finset.univ_nonempty).choose_spec.2 j
    (Finset.mem_univ j)

/-! ## The rule -/

/-- The counts produced by the tracking rule for a target sequence `p`. -/
noncomputable def trackCounts [NeZero k] (p : ℕ → Fin k → ℝ) : ℕ → Fin k → ℕ
  | 0 => fun _ ↦ 0
  | t + 1 => fun j ↦ trackCounts p t j +
      (if j = argMaxArm (fun l ↦ cumTarget p t l - (trackCounts p t l : ℝ))
        then 1 else 0)

/-- The arm the rule plays at round `t`: one of maximal shortfall. -/
noncomputable def trackArm [NeZero k] (p : ℕ → Fin k → ℝ) (t : ℕ) : Fin k :=
  argMaxArm fun l ↦ cumTarget p t l - (trackCounts p t l : ℝ)

@[simp]
theorem trackCounts_zero [NeZero k] (p : ℕ → Fin k → ℝ) (j : Fin k) :
    trackCounts p 0 j = 0 := rfl

theorem trackCounts_succ [NeZero k] (p : ℕ → Fin k → ℝ) (t : ℕ) (j : Fin k) :
    trackCounts p (t + 1) j
      = trackCounts p t j + (if j = trackArm p t then 1 else 0) := rfl

/-- **The rule tracks.**  Immediate from the definitions: the counts increment
the arm the rule plays, and that arm maximises the shortfall. -/
theorem isTracking_trackCounts [NeZero k] (p : ℕ → Fin k → ℝ) :
    IsTracking p (trackCounts p) (trackArm p) where
  init := trackCounts_zero p
  step := trackCounts_succ p
  greedy := fun t j ↦ le_argMaxArm (fun l ↦ cumTarget p t l - (trackCounts p t l : ℝ)) j

/-! ## The rule applied to plug-in optimal allocations -/

/-- The target sequence of D-Tracking: the optimal allocation at the current
estimate, floored at the exploration level. -/
@[reducible] noncomputable def dTrackTarget [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (m : ℕ → Fin k → ℝ) :
    ℕ → Fin k → ℝ :=
  flooredTarget k fun s ↦ optimalAllocation hne (m s)

theorem dTrackTarget_nonneg [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (m : ℕ → Fin k → ℝ) (s : ℕ) (j : Fin k) :
    0 ≤ dTrackTarget hne m s j := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  exact flooredTarget_nonneg hk
    (fun s l ↦ (optimalAllocation_mem hne (m s)).1 l) s j

theorem dTrackTarget_sum [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (m : ℕ → Fin k → ℝ) (s : ℕ) :
    ∑ j, dTrackTarget hne m s j = 1 :=
  flooredTarget_sum (fun s ↦ (optimalAllocation_mem hne (m s)).2) s

/-- The counts produced by D-Tracking from a sequence of estimates. -/
@[reducible] noncomputable def dTrackCounts [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (m : ℕ → Fin k → ℝ) :
    ℕ → Fin k → ℕ :=
  trackCounts (dTrackTarget hne m)

/-! ## Lemma 7: no arm is starved -/

/-- **Every arm is played at least `√(k²+t) − 2k + 1` times by round `t`**, for
any sequence of estimates whatsoever. -/
theorem sqrt_le_dTrackCounts [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (m : ℕ → Fin k → ℝ) (t : ℕ) (j : Fin k) :
    Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - 2 * (k : ℝ) + 1
      ≤ (dTrackCounts hne m t j : ℝ) :=
  sqrt_le_count (isTracking_trackCounts _)
    (fun s l ↦ (optimalAllocation_mem hne (m s)).1 l)
    (fun s ↦ (optimalAllocation_mem hne (m s)).2) t j

/-- The explicit-round form: from round `(M + 2k)²` on, every arm has been played
more than `M` times. -/
theorem lt_dTrackCounts [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (m : ℕ → Fin k → ℝ) {M t : ℕ}
    (ht : forcedTrackRound k M ≤ t) (j : Fin k) : M < dTrackCounts hne m t j :=
  lt_count_of_forcedTrackRound_le (isTracking_trackCounts _)
    (fun s l ↦ (optimalAllocation_mem hne (m s)).1 l)
    (fun s ↦ (optimalAllocation_mem hne (m s)).2) ht j

theorem tendsto_dTrackCounts_atTop [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) (m : ℕ → Fin k → ℝ) (j : Fin k) :
    Tendsto (fun t ↦ dTrackCounts hne m t j) atTop atTop :=
  tendsto_count_atTop (isTracking_trackCounts _)
    (fun s l ↦ (optimalAllocation_mem hne (m s)).1 l)
    (fun s ↦ (optimalAllocation_mem hne (m s)).2) j

/-! ## Lemma 8: the allocation converges -/

/-- The targets converge to the optimal allocation at the limit parameter: the
floor vanishes and the plug-in allocations converge by continuity. -/
theorem tendsto_dTrackTarget [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) (j : Fin k) :
    Tendsto (fun s ↦ dTrackTarget hne m s j) atTop
      (𝓝 (optimalAllocation hne μ j)) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  refine tendsto_mixUniform (tendsto_exploreFloor hk) ?_ j
  exact tendsto_optimal_coord hne hμ hm (fun s ↦ optimalAllocation_spec hne (m s))

/-- **The empirical allocation converges to the optimal one.**  Garivier &
Kaufmann, Lemma 8 with Proposition 9: the tracking bound is `O(1)` while the
horizon grows, so the counts inherit the Cesàro limit of the targets. -/
theorem tendsto_dTrackCounts_div [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) (j : Fin k) :
    Tendsto (fun t ↦ (dTrackCounts hne m t j : ℝ) / (t : ℝ)) atTop
      (𝓝 (optimalAllocation hne μ j)) := by
  refine tendsto_div_of_tracking (tendsto_dTrackTarget hne hμ hm j)
    (C := (k : ℝ)) (M := fun t ↦ (dTrackCounts hne m t j : ℝ)) ?_
  intro t
  exact abs_shortfall_le (isTracking_trackCounts (dTrackTarget hne m))
    (dTrackTarget_nonneg hne m) (dTrackTarget_sum hne m) t j

/-! ## The two guarantees together

The statement a sampling rule is expected to satisfy: it never starves an arm,
and its empirical allocation converges to the optimum.  Both hold for the single
rule `trackArm (dTrackTarget hne m)`, for every sequence of estimates converging
to a parameter with a strictly best arm. -/

theorem dTracking_guarantee [NeZero k] {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j ≠ μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) :
    (∀ (t : ℕ) (j : Fin k), Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - 2 * (k : ℝ) + 1
        ≤ (dTrackCounts hne m t j : ℝ))
      ∧ (∀ j : Fin k, Tendsto (fun t : ℕ ↦ (dTrackCounts hne m t j : ℝ) / (t : ℝ)) atTop
        (𝓝 (optimalAllocation hne μ j))) :=
  ⟨fun t j ↦ sqrt_le_dTrackCounts hne m t j,
   fun j ↦ tendsto_dTrackCounts_div hne hμ hm j⟩

end BanditAlgorithm

/-!
# The D-Tracking rule as a function of the estimates alone

`Solutions/TrackAndStopRule.lean` builds the rule from `dTrackTarget hne`, whose
plug-in step is `optimalAllocation hne`, and `hne : (univ.erase i).Nonempty`
carries the index `i` in its *type*.  The objective
`alloRate hne μ α = min_{j ≠ i} …` is genuinely a function of `i`, so that rule
computes the optimal allocation *for the hypothesis that arm `i` is best*.

That is fine as an analysis device — in the analysis `i` is the true best arm —
but it cannot be a sampling rule: a policy has to be one fixed object, chosen
before the environment, and may not consult the answer.  This file rebuilds the
rule so that it depends on the estimates only, by plugging in the **empirical**
best arm:

  `plugInAllocation m = optimalAllocation (at the argmax of m) m`.

The two agree wherever it matters.  If `m` has a strict maximiser `i` then
`argMaxArm m = i` and the two allocations are literally the same function, so
along estimates converging to a parameter with a strictly best arm the plug-in
targets *eventually* coincide with the analysis targets.  Cesàro limits and
`Tendsto` are insensitive to finitely many terms, so every guarantee transfers.

## What is index-free and what is not

The exploration floor and the tracking step never mention `i`, so the count bound
`T_j(t) ≥ √(k²+t) − 2k + 1` holds for the plug-in rule with *no* hypothesis at
all — as it must, since it is the ingredient that makes the estimates consistent
in the first place and so cannot presuppose them.  Only the Cesàro limit needs
the environment to have a strictly best arm, and there the eventual agreement is
exactly what is used.
-/

open Filter Topology Finset

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## Erasing any index leaves something, once there are two arms -/

theorem erase_nonempty_of_two_le (hk2 : 2 ≤ k) (i : Fin k) :
    (Finset.univ.erase i).Nonempty := by
  classical
  have hcard : 0 < (Finset.univ.erase i).card := by
    have h := Finset.card_erase_of_mem (Finset.mem_univ i)
    rw [h, Finset.card_univ, Fintype.card_fin]
    omega
  exact Finset.card_pos.mp hcard

/-! ## The plug-in allocation

The index is an explicit argument, so that rewriting it is a plain `congrArg`
rather than a transport along a dependent hypothesis. -/

/-- The optimal allocation computed *as if* arm `a` were the best one. -/
noncomputable def alloAt [NeZero k] (hk2 : 2 ≤ k) (a : Fin k) (m : Fin k → ℝ) :
    Fin k → ℝ :=
  optimalAllocation (erase_nonempty_of_two_le hk2 a) m

/-- **The plug-in allocation**: the optimal allocation at the empirical best arm.
A function of the estimates alone. -/
noncomputable def plugInAllocation [NeZero k] (hk2 : 2 ≤ k) (m : Fin k → ℝ) :
    Fin k → ℝ :=
  alloAt hk2 (argMaxArm m) m

/-- `alloAt` does not see which proof of nonemptiness it was handed. -/
theorem alloAt_eq_optimalAllocation [NeZero k] (hk2 : 2 ≤ k) {a : Fin k}
    (hne : (Finset.univ.erase a).Nonempty) (m : Fin k → ℝ) :
    alloAt hk2 a m = optimalAllocation hne m := rfl

/-- A strict maximiser is the arm `argMaxArm` returns. -/
theorem argMaxArm_eq_of_strict_max [NeZero k] {i : Fin k} {m : Fin k → ℝ}
    (hm : ∀ j, j ≠ i → m j < m i) : argMaxArm m = i := by
  by_contra hcon
  exact absurd (le_argMaxArm m i) (not_le.mpr (hm _ hcon))

/-- **Where the best arm is strict, the plug-in rule is the analysis rule.** -/
theorem plugInAllocation_eq_of_strict_max [NeZero k] (hk2 : 2 ≤ k) {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {m : Fin k → ℝ}
    (hm : ∀ j, j ≠ i → m j < m i) :
    plugInAllocation hk2 m = optimalAllocation hne m := by
  unfold plugInAllocation
  rw [argMaxArm_eq_of_strict_max hm]
  exact alloAt_eq_optimalAllocation hk2 hne m

theorem plugInAllocation_mem [NeZero k] (hk2 : 2 ≤ k) (m : Fin k → ℝ) :
    plugInAllocation hk2 m ∈ alloSimplex k :=
  optimalAllocation_mem _ m

theorem plugInAllocation_nonneg [NeZero k] (hk2 : 2 ≤ k) (m : Fin k → ℝ)
    (j : Fin k) : 0 ≤ plugInAllocation hk2 m j :=
  (plugInAllocation_mem hk2 m).1 j

theorem plugInAllocation_sum [NeZero k] (hk2 : 2 ≤ k) (m : Fin k → ℝ) :
    ∑ j, plugInAllocation hk2 m j = 1 :=
  (plugInAllocation_mem hk2 m).2

/-! ## The rule -/

/-- The target sequence of the estimate-driven rule. -/
@[reducible] noncomputable def pTrackTarget [NeZero k] (hk2 : 2 ≤ k)
    (m : ℕ → Fin k → ℝ) : ℕ → Fin k → ℝ :=
  flooredTarget k fun s ↦ plugInAllocation hk2 (m s)

theorem pTrackTarget_nonneg [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ)
    (s : ℕ) (j : Fin k) : 0 ≤ pTrackTarget hk2 m s j := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  exact flooredTarget_nonneg hk (fun s l ↦ plugInAllocation_nonneg hk2 (m s) l) s j

theorem pTrackTarget_sum [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ) (s : ℕ) :
    ∑ j, pTrackTarget hk2 m s j = 1 :=
  flooredTarget_sum (fun s ↦ plugInAllocation_sum hk2 (m s)) s

/-- The counts produced by the estimate-driven rule. -/
@[reducible] noncomputable def pTrackCounts [NeZero k] (hk2 : 2 ≤ k)
    (m : ℕ → Fin k → ℝ) : ℕ → Fin k → ℕ :=
  trackCounts (pTrackTarget hk2 m)

/-- The arm the estimate-driven rule plays at round `t`. -/
noncomputable def pTrackArm [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ)
    (t : ℕ) : Fin k :=
  trackArm (pTrackTarget hk2 m) t

theorem pTrackCounts_zero [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ)
    (j : Fin k) : pTrackCounts hk2 m 0 j = 0 := rfl

theorem pTrackCounts_succ [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ)
    (t : ℕ) (j : Fin k) :
    pTrackCounts hk2 m (t + 1) j
      = pTrackCounts hk2 m t j + (if j = pTrackArm hk2 m t then 1 else 0) := rfl

/-! ## Lemma 7, with no hypothesis on the estimates -/

/-- **No arm is starved**, whatever the estimates are.  The exploration floor is
inside the target, so this is a statement about the tracking step alone. -/
theorem sqrt_le_pTrackCounts [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ)
    (t : ℕ) (j : Fin k) :
    Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - 2 * (k : ℝ) + 1
      ≤ (pTrackCounts hk2 m t j : ℝ) :=
  sqrt_le_count (isTracking_trackCounts _)
    (fun s l ↦ plugInAllocation_nonneg hk2 (m s) l)
    (fun s ↦ plugInAllocation_sum hk2 (m s)) t j

/-! ## The targets converge

This is the only place the environment enters, and it enters only through
"eventually the empirical best arm is the true one". -/

/-- **The plug-in targets converge to the optimal allocation.** -/
theorem tendsto_pTrackTarget [NeZero k] (hk2 : 2 ≤ k) {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j < μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) (j : Fin k) :
    Tendsto (fun s ↦ pTrackTarget hk2 m s j) atTop
      (𝓝 (optimalAllocation hne μ j)) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  refine tendsto_mixUniform (tendsto_exploreFloor hk) ?_ j
  intro l
  -- the analysis targets converge …
  have hbase : Tendsto (fun s ↦ optimalAllocation hne (m s) l) atTop
      (𝓝 (optimalAllocation hne μ l)) :=
    tendsto_optimal_coord hne (fun j hj ↦ (hμ j hj).ne) hm
      (fun s ↦ optimalAllocation_spec hne (m s)) l
  -- … and the plug-in targets eventually agree with them
  refine hbase.congr' ?_
  filter_upwards [eventually_strictly_best_seq hμ hm] with s hs
  exact (congrFun (plugInAllocation_eq_of_strict_max hk2 hne hs) l).symm

/-- **The empirical allocation of the estimate-driven rule converges to the
optimal one.** -/
theorem tendsto_pTrackCounts_div [NeZero k] (hk2 : 2 ≤ k) {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j < μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) (j : Fin k) :
    Tendsto (fun t ↦ (pTrackCounts hk2 m t j : ℝ) / (t : ℝ)) atTop
      (𝓝 (optimalAllocation hne μ j)) := by
  refine tendsto_div_of_tracking (tendsto_pTrackTarget hk2 hne hμ hm j)
    (C := (k : ℝ)) (M := fun t ↦ (pTrackCounts hk2 m t j : ℝ)) ?_
  intro t
  exact abs_shortfall_le (isTracking_trackCounts (pTrackTarget hk2 m))
    (pTrackTarget_nonneg hk2 m) (pTrackTarget_sum hk2 m) t j

/-- **Both guarantees for the estimate-driven rule.** -/
theorem pTracking_guarantee [NeZero k] (hk2 : 2 ≤ k) {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j < μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) :
    (∀ (t : ℕ) (j : Fin k), Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - 2 * (k : ℝ) + 1
        ≤ (pTrackCounts hk2 m t j : ℝ))
      ∧ (∀ j : Fin k, Tendsto (fun t : ℕ ↦ (pTrackCounts hk2 m t j : ℝ) / (t : ℝ))
          atTop (𝓝 (optimalAllocation hne μ j))) :=
  ⟨fun t j ↦ sqrt_le_pTrackCounts hk2 m t j,
   fun j ↦ tendsto_pTrackCounts_div hk2 hne hμ hm j⟩

end BanditAlgorithm

/-!
# A measurable plug-in allocation

`optimalAllocation` is a `Classical.choose` of a maximiser produced by
compactness, so it carries no measurability whatever.  That is harmless for the
*analysis* — every statement there is about limits along a fixed sequence — but a
sampling rule has to be a Markov kernel on histories, and `Kernel.deterministic`
needs a measurable function.

The repair costs nothing, because the choice is only ambiguous where it does not
matter.  Where the estimates have a strictly best arm the maximiser is *unique*
(`eq_of_isOptimal`) and therefore continuous; where they do not, the objective is
degenerate and any probability vector will do.  So define

  `safeAllocation m = plugInAllocation m`   if `m` has a strictly best arm,
  `safeAllocation m = uniform`              otherwise.

The strict set is open — it is a finite union of finite intersections of strict
inequalities — so this is continuous on an open set and constant on the closed
complement, hence measurable.

## Why nothing is lost

Along estimates converging to a parameter with a strictly best arm, the estimates
are *eventually* in the strict set, so `safeAllocation` eventually agrees with
`plugInAllocation`, and `Tendsto` does not see finitely many terms.  The
exploration floor and the count bound never look at the allocation at all beyond
its being a probability vector, which `safeAllocation` is everywhere.
-/

open Filter Topology Finset MeasureTheory

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The strict set -/

/-- Parameters with a strictly best arm. -/
def StrictBestSet (k : ℕ) : Set (Fin k → ℝ) := {m | ∃ i, ∀ j, j ≠ i → m j < m i}

theorem isOpen_strictBestSet : IsOpen (StrictBestSet k) := by
  have hcover : StrictBestSet k = ⋃ i : Fin k, {m : Fin k → ℝ | ∀ j, j ≠ i → m j < m i} := by
    ext m
    simp [StrictBestSet]
  rw [hcover]
  refine isOpen_iUnion fun i ↦ ?_
  have hinter : {m : Fin k → ℝ | ∀ j, j ≠ i → m j < m i}
      = ⋂ j ∈ Finset.univ.erase i, {m : Fin k → ℝ | m j < m i} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_iInter, mem_erase_iff_ne]
  rw [hinter]
  refine isOpen_biInter_finset fun j _ ↦ ?_
  exact isOpen_lt (continuous_apply j) (continuous_apply i)

theorem measurableSet_strictBestSet : MeasurableSet (StrictBestSet k) :=
  isOpen_strictBestSet.measurableSet

/-! ## The uniform allocation -/

/-- The uniform probability vector, used where the objective is degenerate. -/
noncomputable def uniformAllo (k : ℕ) : Fin k → ℝ := fun _ ↦ (k : ℝ)⁻¹

theorem uniformAllo_mem [NeZero k] : uniformAllo k ∈ alloSimplex k := by
  have hk : (0 : ℝ) < (k : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne k)
    exact_mod_cast this
  refine ⟨fun _ ↦ le_of_lt (inv_pos.mpr hk), ?_⟩
  simp only [uniformAllo, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-! ## The measurable selection -/

open scoped Classical in
/-- **The plug-in allocation, made measurable.**  Unchanged where the estimates
have a strictly best arm; uniform where they do not. -/
noncomputable def safeAllocation [NeZero k] (hk2 : 2 ≤ k) (m : Fin k → ℝ) :
    Fin k → ℝ :=
  if m ∈ StrictBestSet k then plugInAllocation hk2 m else uniformAllo k

theorem safeAllocation_of_mem [NeZero k] (hk2 : 2 ≤ k) {m : Fin k → ℝ}
    (hm : m ∈ StrictBestSet k) : safeAllocation hk2 m = plugInAllocation hk2 m := by
  classical
  simp [safeAllocation, hm]

/-- **Where the best arm is strict, the measurable rule is the analysis rule.** -/
theorem safeAllocation_eq_of_strict_max [NeZero k] (hk2 : 2 ≤ k) {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {m : Fin k → ℝ}
    (hm : ∀ j, j ≠ i → m j < m i) :
    safeAllocation hk2 m = optimalAllocation hne m := by
  rw [safeAllocation_of_mem hk2 ⟨i, hm⟩, plugInAllocation_eq_of_strict_max hk2 hne hm]

theorem safeAllocation_mem [NeZero k] (hk2 : 2 ≤ k) (m : Fin k → ℝ) :
    safeAllocation hk2 m ∈ alloSimplex k := by
  classical
  by_cases hm : m ∈ StrictBestSet k
  · rw [safeAllocation_of_mem hk2 hm]; exact plugInAllocation_mem hk2 m
  · simp only [safeAllocation, if_neg hm]; exact uniformAllo_mem

theorem safeAllocation_nonneg [NeZero k] (hk2 : 2 ≤ k) (m : Fin k → ℝ) (j : Fin k) :
    0 ≤ safeAllocation hk2 m j := (safeAllocation_mem hk2 m).1 j

theorem safeAllocation_sum [NeZero k] (hk2 : 2 ≤ k) (m : Fin k → ℝ) :
    ∑ j, safeAllocation hk2 m j = 1 := (safeAllocation_mem hk2 m).2

/-! ## Continuity on the strict set -/

/-- On the strict set the plug-in allocation is the canonical optimal
allocation at the (locally constant) empirical best arm, hence continuous. -/
theorem continuousAt_plugInAllocation [NeZero k] (hk2 : 2 ≤ k) {μ : Fin k → ℝ}
    (hμ : μ ∈ StrictBestSet k) : ContinuousAt (plugInAllocation hk2) μ := by
  obtain ⟨i, hi⟩ := hμ
  have hne : (Finset.univ.erase i).Nonempty := erase_nonempty_of_two_le hk2 i
  have hbase : ContinuousAt (optimalAllocation hne) μ :=
    continuousAt_optimalAllocation hne (fun j hj ↦ (hi j hj).ne)
  refine hbase.congr ?_
  filter_upwards [eventually_strictly_best hi] with m hm
  exact (plugInAllocation_eq_of_strict_max hk2 hne hm).symm

theorem continuousOn_plugInAllocation [NeZero k] (hk2 : 2 ≤ k) :
    ContinuousOn (plugInAllocation hk2) (StrictBestSet k) := fun μ hμ ↦
  (continuousAt_plugInAllocation hk2 hμ).continuousWithinAt

/-! ## Measurability -/

theorem measurable_safeAllocation [NeZero k] (hk2 : 2 ≤ k) :
    Measurable (safeAllocation hk2) := by
  classical
  refine measurable_of_restrict_of_restrict_compl measurableSet_strictBestSet ?_ ?_
  · -- on the strict set: continuous
    have hcont : ContinuousOn (safeAllocation hk2) (StrictBestSet k) := by
      refine (continuousOn_plugInAllocation hk2).congr fun m hm ↦ ?_
      exact safeAllocation_of_mem hk2 hm
    exact hcont.restrict.measurable
  · -- off it: constant
    have hconst : (StrictBestSet k)ᶜ.domRestrict (safeAllocation hk2)
        = fun _ ↦ uniformAllo k := by
      funext m
      simp only [Set.domRestrict_apply, safeAllocation]
      rw [if_neg m.2]
    rw [hconst]
    exact measurable_const

end BanditAlgorithm

/-!
# A canonical, measurable maximiser

`argMaxArm` (`Solutions/TrackAndStopRule.lean`) is a `Classical.choose` of a
maximal coordinate.  For the *analysis* that is enough — the tracking bound only
needs the played arm to be **some** maximiser of the shortfall — but the sampling
rule has to be a measurable function of the history, and an arbitrary choice
among tied maximisers has no measurability.

Breaking ties by least index repairs this.  The fibre of `leastArgMax` is

  `{f | (∀ j, f j ≤ f i) ∧ ∀ i', (∀ j, f j ≤ f i') → i ≤ i'}`,

a finite intersection of closed half-spaces and their complements, so it is
measurable; and `Fin k` is countable, so measurability of every fibre is
measurability.

This is the same device that makes `chernoffRecommendation` measurable — there
the tie-breaking is invisible because the statistic vanishes at a tie, here it is
invisible because the tracking bound is indifferent to which maximiser is played.
-/

open Filter Topology Finset MeasureTheory

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The maximiser set -/

/-- The coordinates at which `f` attains its maximum. -/
noncomputable def maxArms [NeZero k] (f : Fin k → ℝ) : Finset (Fin k) :=
  Finset.univ.filter fun i ↦ ∀ j, f j ≤ f i

theorem mem_maxArms [NeZero k] {f : Fin k → ℝ} {i : Fin k} :
    i ∈ maxArms f ↔ ∀ j, f j ≤ f i := by
  classical
  simp [maxArms]

theorem maxArms_nonempty [NeZero k] (f : Fin k → ℝ) : (maxArms f).Nonempty := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  exact ⟨i, mem_maxArms.mpr fun j ↦ hi j (Finset.mem_univ j)⟩

/-! ## The canonical maximiser -/

/-- The least maximal coordinate of `f`. -/
noncomputable def leastArgMax [NeZero k] (f : Fin k → ℝ) : Fin k :=
  (maxArms f).min' (maxArms_nonempty f)

theorem le_leastArgMax [NeZero k] (f : Fin k → ℝ) (j : Fin k) :
    f j ≤ f (leastArgMax f) :=
  mem_maxArms.mp ((maxArms f).min'_mem (maxArms_nonempty f)) j

theorem leastArgMax_le [NeZero k] {f : Fin k → ℝ} {i : Fin k}
    (hi : ∀ j, f j ≤ f i) : leastArgMax f ≤ i :=
  (maxArms f).min'_le i (mem_maxArms.mpr hi)

/-- The defining property, as an iff — this is what identifies the fibres. -/
theorem leastArgMax_eq_iff [NeZero k] {f : Fin k → ℝ} {i : Fin k} :
    leastArgMax f = i ↔ (∀ j, f j ≤ f i) ∧ ∀ i', (∀ j, f j ≤ f i') → i ≤ i' := by
  constructor
  · rintro rfl
    exact ⟨le_leastArgMax f, fun i' hi' ↦ leastArgMax_le hi'⟩
  · rintro ⟨hmax, hmin⟩
    exact le_antisymm (leastArgMax_le hmax) (hmin _ (le_leastArgMax f))

/-! ## Measurability -/

theorem measurableSet_le_coord (i j : Fin k) :
    MeasurableSet {f : Fin k → ℝ | f j ≤ f i} :=
  measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)

theorem measurable_leastArgMax [NeZero k] :
    Measurable (leastArgMax : (Fin k → ℝ) → Fin k) := by
  classical
  refine measurable_to_countable' fun i ↦ ?_
  have hfib : (leastArgMax ⁻¹' {i} : Set (Fin k → ℝ))
      = (⋂ j : Fin k, {f : Fin k → ℝ | f j ≤ f i})
        ∩ ⋂ i' ∈ Finset.univ.filter (fun i' : Fin k ↦ ¬ i ≤ i'),
            (⋂ j : Fin k, {f : Fin k → ℝ | f j ≤ f i'})ᶜ := by
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_setOf_eq, Set.mem_compl_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [leastArgMax_eq_iff]
    constructor
    · rintro ⟨hmax, hmin⟩
      exact ⟨hmax, fun i' hi' hcon ↦ hi' (hmin i' hcon)⟩
    · rintro ⟨hmax, hmin⟩
      refine ⟨hmax, fun i' hi' ↦ ?_⟩
      by_contra hcon
      exact hmin i' hcon hi'
  rw [hfib]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun j ↦ measurableSet_le_coord i j
  · refine MeasurableSet.biInter (Finset.univ.filter
      (fun i' : Fin k ↦ ¬ i ≤ i')).countable_toSet fun i' _ ↦ ?_
    exact (MeasurableSet.iInter fun j ↦ measurableSet_le_coord i' j).compl

end BanditAlgorithm

/-!
# The D-Tracking rule with every choice made canonically

Two arbitrary choices stood between the analysis rule of
`Solutions/TrackAndStopRule.lean` and an actual sampling rule: the maximiser of
the shortfall (`argMaxArm`) and the optimal allocation at the current estimates
(`optimalAllocation`, a compactness `Classical.choose`).  Both have been replaced
— by `leastArgMax` (`Solutions/CanonicalArgmax.lean`) and by `safeAllocation`
(`Solutions/PlugInMeasurable.lean`) — and this file assembles the resulting rule
and reproves its two guarantees.

Neither replacement costs anything:

* the tracking bound `|N_i(t) − ∑_{s<t} p_i(s)| ≤ k` and the exploration bound
  `N_i(t) ≥ √(k²+t) − 2k + 1` are proved from the `IsTracking` interface, which
  asks only that the played arm be *a* maximiser of the shortfall — so they
  transfer verbatim;
* `safeAllocation` differs from the analysis allocation only off the strict set,
  and along estimates converging to a parameter with a strictly best arm the
  estimates are eventually inside it.

## Prefix determinacy

The last section is what makes this a *policy* rather than a rule on sequences:
the arm played at round `t` reads the target only at rounds `s < t`, hence the
estimates only at rounds `s < t`, hence the history only up to round `t`.  This
is the statement that lets the rule be evaluated on a `BanditHistory k t`, and
it is proved by the obvious induction — the recursion for the counts consumes
`cumTarget p t`, a sum over `Finset.range t`.
-/

open Filter Topology Finset MeasureTheory

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The rule, with canonical tie-breaking -/

/-- The counts produced by the tracking rule, ties broken by least index. -/
noncomputable def sTrackCounts [NeZero k] (p : ℕ → Fin k → ℝ) : ℕ → Fin k → ℕ
  | 0 => fun _ ↦ 0
  | t + 1 => fun j ↦ sTrackCounts p t j +
      (if j = leastArgMax (fun l ↦ cumTarget p t l - (sTrackCounts p t l : ℝ))
        then 1 else 0)

/-- The arm the rule plays at round `t`: the least of maximal shortfall. -/
noncomputable def sTrackArm [NeZero k] (p : ℕ → Fin k → ℝ) (t : ℕ) : Fin k :=
  leastArgMax fun l ↦ cumTarget p t l - (sTrackCounts p t l : ℝ)

@[simp]
theorem sTrackCounts_zero [NeZero k] (p : ℕ → Fin k → ℝ) (j : Fin k) :
    sTrackCounts p 0 j = 0 := rfl

theorem sTrackCounts_succ [NeZero k] (p : ℕ → Fin k → ℝ) (t : ℕ) (j : Fin k) :
    sTrackCounts p (t + 1) j
      = sTrackCounts p t j + (if j = sTrackArm p t then 1 else 0) := rfl

theorem isTracking_sTrackCounts [NeZero k] (p : ℕ → Fin k → ℝ) :
    IsTracking p (sTrackCounts p) (sTrackArm p) where
  init := sTrackCounts_zero p
  step := sTrackCounts_succ p
  greedy := fun t j ↦ le_leastArgMax (fun l ↦ cumTarget p t l - (sTrackCounts p t l : ℝ)) j

/-! ## The rule driven by the measurable plug-in allocation -/

/-- The target sequence: the measurable plug-in allocation, floored at the
exploration level. -/
@[reducible] noncomputable def safeTarget [NeZero k] (hk2 : 2 ≤ k)
    (m : ℕ → Fin k → ℝ) : ℕ → Fin k → ℝ :=
  flooredTarget k fun s ↦ safeAllocation hk2 (m s)

theorem safeTarget_nonneg [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ)
    (s : ℕ) (j : Fin k) : 0 ≤ safeTarget hk2 m s j := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  exact flooredTarget_nonneg hk (fun s l ↦ safeAllocation_nonneg hk2 (m s) l) s j

theorem safeTarget_sum [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ) (s : ℕ) :
    ∑ j, safeTarget hk2 m s j = 1 :=
  flooredTarget_sum (fun s ↦ safeAllocation_sum hk2 (m s)) s

/-- The counts produced by the sampling rule. -/
@[reducible] noncomputable def safeCounts [NeZero k] (hk2 : 2 ≤ k)
    (m : ℕ → Fin k → ℝ) : ℕ → Fin k → ℕ :=
  sTrackCounts (safeTarget hk2 m)

/-- The arm the sampling rule plays at round `t`. -/
noncomputable def safeArm [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ)
    (t : ℕ) : Fin k :=
  sTrackArm (safeTarget hk2 m) t

/-! ## Lemma 7, with no hypothesis on the estimates -/

/-- **No arm is starved.** -/
theorem sqrt_le_safeCounts [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ)
    (t : ℕ) (j : Fin k) :
    Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - 2 * (k : ℝ) + 1
      ≤ (safeCounts hk2 m t j : ℝ) :=
  sqrt_le_count (isTracking_sTrackCounts _)
    (fun s l ↦ safeAllocation_nonneg hk2 (m s) l)
    (fun s ↦ safeAllocation_sum hk2 (m s)) t j

/-! ## The Cesàro limit -/

/-- **The targets converge to the optimal allocation.** -/
theorem tendsto_safeTarget [NeZero k] (hk2 : 2 ≤ k) {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j < μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) (j : Fin k) :
    Tendsto (fun s ↦ safeTarget hk2 m s j) atTop
      (𝓝 (optimalAllocation hne μ j)) := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  refine tendsto_mixUniform (tendsto_exploreFloor hk) ?_ j
  intro l
  have hbase : Tendsto (fun s ↦ optimalAllocation hne (m s) l) atTop
      (𝓝 (optimalAllocation hne μ l)) :=
    tendsto_optimal_coord hne (fun j hj ↦ (hμ j hj).ne) hm
      (fun s ↦ optimalAllocation_spec hne (m s)) l
  refine hbase.congr' ?_
  filter_upwards [eventually_strictly_best_seq hμ hm] with s hs
  exact (congrFun (safeAllocation_eq_of_strict_max hk2 hne hs) l).symm

/-- **The empirical allocation converges to the optimal one.** -/
theorem tendsto_safeCounts_div [NeZero k] (hk2 : 2 ≤ k) {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j < μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) (j : Fin k) :
    Tendsto (fun t ↦ (safeCounts hk2 m t j : ℝ) / (t : ℝ)) atTop
      (𝓝 (optimalAllocation hne μ j)) := by
  refine tendsto_div_of_tracking (tendsto_safeTarget hk2 hne hμ hm j)
    (C := (k : ℝ)) (M := fun t ↦ (safeCounts hk2 m t j : ℝ)) ?_
  intro t
  exact abs_shortfall_le (isTracking_sTrackCounts (safeTarget hk2 m))
    (safeTarget_nonneg hk2 m) (safeTarget_sum hk2 m) t j

/-- **Both guarantees for the sampling rule.** -/
theorem safeTracking_guarantee [NeZero k] (hk2 : 2 ≤ k) {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j < μ i) {m : ℕ → Fin k → ℝ}
    (hm : Tendsto m atTop (𝓝 μ)) :
    (∀ (t : ℕ) (j : Fin k), Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - 2 * (k : ℝ) + 1
        ≤ (safeCounts hk2 m t j : ℝ))
      ∧ (∀ j : Fin k, Tendsto (fun t : ℕ ↦ (safeCounts hk2 m t j : ℝ) / (t : ℝ))
          atTop (𝓝 (optimalAllocation hne μ j))) :=
  ⟨fun t j ↦ sqrt_le_safeCounts hk2 m t j,
   fun j ↦ tendsto_safeCounts_div hk2 hne hμ hm j⟩

/-! ## Prefix determinacy

Round `t` reads the target only at rounds `s < t`. -/

theorem cumTarget_congr {p q : ℕ → Fin k → ℝ} {t : ℕ}
    (h : ∀ s, s < t → p s = q s) : cumTarget p t = cumTarget q t := by
  funext i
  unfold cumTarget
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [h s (Finset.mem_range.mp hs)]

theorem sTrackCounts_congr [NeZero k] {p q : ℕ → Fin k → ℝ} :
    ∀ {t : ℕ}, (∀ s, s < t → p s = q s) → sTrackCounts p t = sTrackCounts q t
  | 0, _ => rfl
  | t + 1, h => by
      have hlt : ∀ s, s < t → p s = q s := fun s hs ↦ h s (Nat.lt_succ_of_lt hs)
      have hcounts : sTrackCounts p t = sTrackCounts q t := sTrackCounts_congr hlt
      have hcum : cumTarget p t = cumTarget q t := cumTarget_congr hlt
      funext j
      show sTrackCounts p t j + _ = sTrackCounts q t j + _
      rw [hcounts, hcum]

theorem sTrackArm_congr [NeZero k] {p q : ℕ → Fin k → ℝ} {t : ℕ}
    (h : ∀ s, s < t → p s = q s) : sTrackArm p t = sTrackArm q t := by
  unfold sTrackArm
  rw [sTrackCounts_congr h, cumTarget_congr h]

/-- **The played arm depends on the estimates only up to the current round.**
This is what allows the rule to be evaluated on a finite history. -/
theorem safeArm_congr [NeZero k] (hk2 : 2 ≤ k) {m m' : ℕ → Fin k → ℝ} {t : ℕ}
    (h : ∀ s, s < t → m s = m' s) : safeArm hk2 m t = safeArm hk2 m' t := by
  refine sTrackArm_congr fun s hs ↦ ?_
  have heq : safeAllocation hk2 (m s) = safeAllocation hk2 (m' s) := by rw [h s hs]
  funext i
  simp only [safeTarget, flooredTarget, heq]

theorem safeCounts_congr [NeZero k] (hk2 : 2 ≤ k) {m m' : ℕ → Fin k → ℝ} {t : ℕ}
    (h : ∀ s, s < t → m s = m' s) : safeCounts hk2 m t = safeCounts hk2 m' t := by
  refine sTrackCounts_congr fun s hs ↦ ?_
  have heq : safeAllocation hk2 (m s) = safeAllocation hk2 (m' s) := by rw [h s hs]
  funext i
  simp only [safeTarget, flooredTarget, heq]

end BanditAlgorithm

/-!
# The rule is a measurable function of the estimates

Everything the rule is built from is now measurable — `safeAllocation`
(`Solutions/PlugInMeasurable.lean`) and `leastArgMax`
(`Solutions/CanonicalArgmax.lean`) — so the counts and the played arm are too,
by the induction that mirrors their recursion.

The only points worth naming:

* the exploration floor is a *constant* at each round, so the target is an affine
  function of the allocation and inherits its measurability;
* `cumTarget` is a finite sum, hence measurable coordinatewise;
* `Fin k` and `ℕ` carry the discrete σ-algebra, so every function *out* of them
  is measurable — which is what makes the tie-breaking indicator and the
  `ℕ → ℝ` cast free.

The induction is on the round, with the arm at round `t` derived from the counts
at round `t` inside the successor step; they cannot be separated, since the
recursion for the counts consumes the arm and the arm consumes the counts.
-/

open Filter Topology Finset MeasureTheory

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The target -/

theorem measurable_safeTarget_apply [NeZero k] (hk2 : 2 ≤ k) (s : ℕ) (i : Fin k) :
    Measurable fun m : ℕ → Fin k → ℝ ↦ safeTarget hk2 m s i := by
  have hbase : Measurable fun m : ℕ → Fin k → ℝ ↦ safeAllocation hk2 (m s) i :=
    ((measurable_pi_apply i).comp (measurable_safeAllocation hk2)).comp
      (measurable_pi_apply s)
  simpa only [safeTarget, flooredTarget, mixUniform, Pi.add_def, Function.comp_def] using
    (hbase.const_mul (1 - (k : ℝ) * exploreFloor k s)).add_const (exploreFloor k s)

theorem measurable_cumTarget_apply [NeZero k] (hk2 : 2 ≤ k) (t : ℕ) (i : Fin k) :
    Measurable fun m : ℕ → Fin k → ℝ ↦ cumTarget (safeTarget hk2 m) t i := by
  unfold cumTarget
  exact Finset.measurable_sum _ fun s _ ↦ measurable_safeTarget_apply hk2 s i

/-! ## The counts and the played arm -/

/-- The arm is measurable as soon as the counts at the same round are. -/
theorem measurable_safeArm_of_counts [NeZero k] (hk2 : 2 ≤ k) {t : ℕ}
    (hC : ∀ l, Measurable fun m : ℕ → Fin k → ℝ ↦ safeCounts hk2 m t l) :
    Measurable fun m : ℕ → Fin k → ℝ ↦ safeArm hk2 m t := by
  have hshort : Measurable fun m : ℕ → Fin k → ℝ ↦
      fun l ↦ cumTarget (safeTarget hk2 m) t l - (safeCounts hk2 m t l : ℝ) := by
    refine measurable_pi_lambda _ fun l ↦ ?_
    exact (measurable_cumTarget_apply hk2 t l).sub (Measurable.of_discrete.comp (hC l))
  exact measurable_leastArgMax.comp hshort

theorem measurable_safeCounts_apply [NeZero k] (hk2 : 2 ≤ k) :
    ∀ (t : ℕ) (j : Fin k), Measurable fun m : ℕ → Fin k → ℝ ↦ safeCounts hk2 m t j
  | 0, j => by
      simpa only [safeCounts, sTrackCounts_zero] using
        (measurable_const : Measurable fun _ : ℕ → Fin k → ℝ ↦ (0 : ℕ))
  | t + 1, j => by
      have hC : ∀ l, Measurable fun m : ℕ → Fin k → ℝ ↦ safeCounts hk2 m t l :=
        fun l ↦ measurable_safeCounts_apply hk2 t l
      have harm : Measurable fun m : ℕ → Fin k → ℝ ↦ safeArm hk2 m t :=
        measurable_safeArm_of_counts hk2 hC
      have hind : Measurable fun m : ℕ → Fin k → ℝ ↦
          (if j = safeArm hk2 m t then 1 else 0 : ℕ) :=
        (Measurable.of_discrete (f := fun a : Fin k ↦ if j = a then (1 : ℕ) else 0)).comp harm
      have hsum := (hC j).add hind
      simp only [safeCounts, sTrackCounts_succ, safeArm]
      convert hsum using 1
      funext m
      simp only [Pi.add_apply]
      congr

theorem measurable_safeArm [NeZero k] (hk2 : 2 ≤ k) (t : ℕ) :
    Measurable fun m : ℕ → Fin k → ℝ ↦ safeArm hk2 m t :=
  measurable_safeArm_of_counts hk2 fun l ↦ measurable_safeCounts_apply hk2 t l

end BanditAlgorithm

/-!
# Measurability of the Track-and-Stop trajectory statistics

Everything Algorithm 21 computes at the end of round `t` is a function of the
first `t` rounds, hence `banditFiltration k t`-measurable.  This file proves that,
for each statistic of `Def_TrackAndStop`, and deduces the two structural clauses
of L&S Lemma 33.7:

* `isBanditStoppingTime_chernoffStoppingTime` — Chernoff's rule really is a
  stopping time of the natural filtration;
* `measurable_chernoffRecommendation` — the recommended arm is measurable with
  respect to the stopping-time σ-algebra `𝓕_τ`.

The only delicate point is that `trajEmpiricalBestArm` is defined through
`Finset.exists_max_image`, i.e. through `Classical.choose`, which carries no
measurability whatsoever.  It is handled in §3: we introduce the *canonical*
(least-index) maximiser `trajArgmax`, which is manifestly measurable, and show
that `trajGLR` — the only consumer of `trajEmpiricalBestArm` — is unchanged when
the canonical maximiser is substituted.  The proof splits on whether the maximum
is attained twice: if it is, both versions of `trajGLR` vanish (the pair term for
the two tied maximisers is `0`), and if it is not, the two maximisers coincide.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Generic comap measurability -/

/-- `Nat.cast : ℕ → ℝ` is measurable (source σ-algebra is `⊤`). -/
theorem measurable_natCast_real : Measurable (fun n : ℕ ↦ (n : ℝ)) :=
  measurable_from_top


/-- A function that factors through `g` is measurable for the σ-algebra `g`
pulls back. -/
theorem measurable_comap_comp {α β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {g : α → β} {f : β → γ} (hf : Measurable f) :
    Measurable[MeasurableSpace.comap g inferInstance] (fun a ↦ f (g a)) :=
  fun _ hs ↦ ⟨f ⁻¹' _, hf hs, rfl⟩

/-- The coordinate `ω s` is `𝓕_t`-measurable as soon as round `s` is among the
first `t`. -/
theorem measurable_trajCoord {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ ω s) := by
  have : (fun ω : ℕ → Fin k × ℝ ↦ ω s) =
      (fun h : BanditHistory k t ↦ h ⟨s, hs⟩) ∘ banditTrajPrefix k t := rfl
  rw [this]
  exact measurable_comap_comp (measurable_pi_apply _)

/-- The arm played in round `s` is `𝓕_t`-measurable for `s < t`. -/
theorem measurable_trajArm {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ (ω s).1) :=
  measurable_fst.comp (measurable_trajCoord hs)

/-- The reward observed in round `s` is `𝓕_t`-measurable for `s < t`. -/
theorem measurable_trajReward {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ (ω s).2) :=
  measurable_snd.comp (measurable_trajCoord hs)

/-! ## 2. The elementary statistics -/

/-- `T_i(t)` is `𝓕_t`-measurable. -/
theorem measurable_trajPullCount (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajPullCount i t) := by
  classical
  -- the count is a finite sum of indicators of `𝓕_t`-measurable events
  have hrw : trajPullCount i t =
      fun ω : ℕ → Fin k × ℝ ↦ ∑ s ∈ Finset.range t, if (ω s).1 = i then 1 else 0 := by
    funext ω
    rw [trajPullCount, Finset.card_filter]
  rw [hrw]
  refine Finset.measurable_sum _ fun s hs ↦ ?_
  have hs' : s < t := Finset.mem_range.mp hs
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_trajArm hs') (measurableSet_singleton i)

/-- The running sum of the rewards collected from arm `i` is `𝓕_t`-measurable. -/
theorem measurable_trajRewardSum (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) := by
  classical
  have hrw : (fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) =
      fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ Finset.range t, if (ω s).1 = i then (ω s).2 else 0 := by
    funext ω
    rw [Finset.sum_filter]
  rw [hrw]
  refine Finset.measurable_sum _ fun s hs ↦ ?_
  have hs' : s < t := Finset.mem_range.mp hs
  exact Measurable.ite ((measurable_trajArm hs') (measurableSet_singleton i))
    (measurable_trajReward hs') measurable_const

/-- `μ̂_i(t)` is `𝓕_t`-measurable. -/
theorem measurable_trajEmpiricalMean (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajEmpiricalMean i t) := by
  have hrw : trajEmpiricalMean i t = fun ω : ℕ → Fin k × ℝ ↦
      (∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) /
        ((trajPullCount i t ω : ℕ) : ℝ) := rfl
  rw [hrw]
  exact (measurable_trajRewardSum i t).div
    (measurable_natCast_real.comp (measurable_trajPullCount i t))

/-- `T_i(t)/t` is `𝓕_t`-measurable. -/
theorem measurable_trajAllocation (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajAllocation i t) := by
  have hrw : trajAllocation i t = fun ω : ℕ → Fin k × ℝ ↦
      ((trajPullCount i t ω : ℕ) : ℝ) / (t : ℝ) := rfl
  rw [hrw]
  exact (measurable_natCast_real.comp (measurable_trajPullCount i t)).div measurable_const

/-- The pairwise GLR statistic is `𝓕_t`-measurable. -/
theorem measurable_trajPairGLR (a b : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajPairGLR a b t) := by
  have hrw : trajPairGLR a b t = fun ω : ℕ → Fin k × ℝ ↦
      ((trajPullCount a t ω : ℕ) : ℝ) * ((trajPullCount b t ω : ℕ) : ℝ) /
          (((trajPullCount a t ω : ℕ) : ℝ) + ((trajPullCount b t ω : ℕ) : ℝ)) *
        (trajEmpiricalMean a t ω - trajEmpiricalMean b t ω) ^ 2 / 2 := rfl
  rw [hrw]
  have hTa : Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount a t ω : ℕ) : ℝ)) :=
    measurable_natCast_real.comp (measurable_trajPullCount a t)
  have hTb : Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount b t ω : ℕ) : ℝ)) :=
    measurable_natCast_real.comp (measurable_trajPullCount b t)
  exact ((((hTa.mul hTb).div (hTa.add hTb)).mul
    (((measurable_trajEmpiricalMean a t).sub
      (measurable_trajEmpiricalMean b t)).pow_const 2)).div measurable_const)

/-! ## 3. The canonical maximiser and tie-independence of `Z_t` -/

section Argmax

variable [NeZero k]

/-- The *canonical* empirical best arm: the least index at which the empirical
mean is maximal.  Unlike `trajEmpiricalBestArm`, which is defined through
`Classical.choose`, this one is measurable. -/
noncomputable def trajArgmax (t : ℕ) (ω : ℕ → Fin k × ℝ) : Fin k :=
  ((Finset.univ : Finset (Fin k)).filter fun i ↦
      ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω).min'
    (by
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
        (fun i ↦ trajEmpiricalMean i t ω) Finset.univ_nonempty
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j ↦ hi j (Finset.mem_univ j)⟩⟩)

theorem trajArgmax_mem_filter (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajArgmax t ω ∈ (Finset.univ : Finset (Fin k)).filter fun i ↦
      ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω :=
  Finset.min'_mem _ _

/-- `trajArgmax` is a maximiser. -/
theorem trajArgmax_spec (t : ℕ) (ω : ℕ → Fin k × ℝ) (j : Fin k) :
    trajEmpiricalMean j t ω ≤ trajEmpiricalMean (trajArgmax t ω) t ω :=
  (Finset.mem_filter.mp (trajArgmax_mem_filter t ω)).2 j

/-- `trajArgmax` is the *least* maximiser. -/
theorem trajArgmax_le (t : ℕ) (ω : ℕ → Fin k × ℝ) {i : Fin k}
    (hi : ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω) :
    trajArgmax t ω ≤ i :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

/-- The canonical maximiser is measurable: its level sets are cut out by finitely
many inequalities between the (measurable) empirical means. -/
theorem measurable_trajArgmax (t : ℕ) :
    Measurable[banditFiltration k t] (trajArgmax (k := k) t) := by
  classical
  have hle : ∀ a b : Fin k, MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | trajEmpiricalMean a t ω ≤ trajEmpiricalMean b t ω} := fun a b ↦
    measurableSet_le (measurable_trajEmpiricalMean a t) (measurable_trajEmpiricalMean b t)
  have hmax : ∀ i : Fin k, MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} := by
    intro i
    have hrw : {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω}
        = ⋂ j : Fin k,
          {ω : ℕ → Fin k × ℝ | trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} := by
      ext ω; simp
    rw [hrw]
    exact MeasurableSet.iInter fun j ↦ hle j i
  refine @measurable_to_countable' (Fin k) _ _ _ (banditFiltration k t) _ fun i ↦ ?_
  have hset : (trajArgmax (k := k) t) ⁻¹' {i} =
      {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} ∩
        ⋂ j ∈ {j : Fin k | j < i},
          {ω : ℕ → Fin k × ℝ | ∀ l, trajEmpiricalMean l t ω ≤ trajEmpiricalMean j t ω}ᶜ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨trajArgmax_spec t ω, fun j hj hjmax ↦ ?_⟩
      exact absurd (trajArgmax_le t ω hjmax) (not_le.mpr hj)
    · rintro ⟨himax, hmin⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hmin _ h (trajArgmax_spec t ω)
      · exact absurd (trajArgmax_le t ω himax) (not_le.mpr h)
  rw [hset]
  refine (hmax i).inter (MeasurableSet.biInter (Set.to_countable _) fun j _ ↦ (hmax j).compl)

end Argmax

end BanditAlgorithm

/-!
# The estimates a plug-in rule is driven by

A one-line definition, split out so that the policy construction does not have to
depend on the whole Track-and-Stop settling development just to name the
trajectory's empirical means.
-/

open MeasureTheory Filter Finset

namespace BanditAlgorithm

variable {k : ℕ}

/-- The estimates the rule is driven by: the trajectory's empirical means. -/
noncomputable def trajMeans (ω : ℕ → Fin k × ℝ) (s : ℕ) (l : Fin k) : ℝ :=
  trajEmpiricalMean l s ω

end BanditAlgorithm

/-!
# The sampling rule as a `BanditPolicy`

Everything is in place: the rule is a deterministic function of the estimates
(`Solutions/SafeRule.lean`), it is measurable (`Solutions/SafeRuleMeasurable.lean`),
and it reads the estimates only at rounds strictly before the current one
(prefix determinacy, same file).  So it can be evaluated on a finite history and
packaged as a policy whose every selection kernel is `Kernel.deterministic`.

## Padding

`safeArm` is a function of an *infinite* sequence of estimates, while a history
is finite.  `histExtend` pads the history with a junk round, and prefix
determinacy says the padding is never read: round `n` consumes the estimates only
at rounds `s < n`, and those are computed from the genuine part of the history.
`safeArmOfHistory_prefix` is the statement that makes this precise — evaluating
the rule on the length-`n` prefix of a trajectory gives the same arm as
evaluating it on the trajectory itself.

## Why deterministic

Nothing forces the policy to be deterministic; a randomised rule would do as
well, and would replace the tracking bound by a martingale law of large numbers.
The deterministic version is chosen because the tracking bound
`|N_i(t) − ∑_{s<t} p_i(s)| ≤ k` is already proved and is sharper than anything a
randomised rule would give.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## Padding a history -/

/-- An arbitrary arm, used to pad. -/
def defaultArm (k : ℕ) [NeZero k] : Fin k :=
  ⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩

/-- A finite history, extended to a trajectory by a junk round. -/
def histExtend [NeZero k] (n : ℕ) (h : BanditHistory k n) : ℕ → Fin k × ℝ :=
  fun t ↦ if ht : t < n then h ⟨t, ht⟩ else (defaultArm k, 0)

theorem measurable_histExtend [NeZero k] (n : ℕ) :
    Measurable (histExtend (k := k) n) := by
  refine measurable_pi_lambda _ fun t ↦ ?_
  unfold histExtend
  by_cases ht : t < n
  · simp only [dif_pos ht]
    exact measurable_pi_apply _
  · simp only [dif_neg ht]
    exact measurable_const

/-- On its genuine part the padding is the identity. -/
theorem histExtend_prefix [NeZero k] {n : ℕ} (ω : ℕ → Fin k × ℝ) {t : ℕ}
    (ht : t < n) : histExtend n (banditTrajPrefix k n ω) t = ω t := by
  unfold histExtend banditTrajPrefix
  simp only [dif_pos ht]

/-! ## The trajectory statistics read only the rounds before them -/

theorem trajPullCount_congr (i : Fin k) (t : ℕ) {ω ω' : ℕ → Fin k × ℝ}
    (h : ∀ s, s < t → ω s = ω' s) : trajPullCount i t ω = trajPullCount i t ω' := by
  unfold trajPullCount
  congr 1
  refine Finset.filter_congr fun s hs ↦ ?_
  rw [h s (Finset.mem_range.mp hs)]

theorem trajEmpiricalMean_congr (i : Fin k) (t : ℕ) {ω ω' : ℕ → Fin k × ℝ}
    (h : ∀ s, s < t → ω s = ω' s) :
    trajEmpiricalMean i t ω = trajEmpiricalMean i t ω' := by
  unfold trajEmpiricalMean
  have hfilter : (Finset.range t).filter (fun s ↦ (ω s).1 = i)
      = (Finset.range t).filter fun s ↦ (ω' s).1 = i := by
    refine Finset.filter_congr fun s hs ↦ ?_
    rw [h s (Finset.mem_range.mp hs)]
  rw [trajPullCount_congr i t h, hfilter]
  congr 1
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [h s (Finset.mem_range.mp (Finset.mem_filter.mp hs).1)]

/-! ## The estimates as a function of the history -/

/-- The empirical means read off a finite history. -/
noncomputable def histMeans [NeZero k] (n : ℕ) (h : BanditHistory k n) :
    ℕ → Fin k → ℝ :=
  trajMeans (histExtend n h)

theorem measurable_histMeans [NeZero k] (n : ℕ) :
    Measurable (histMeans (k := k) n) := by
  refine measurable_pi_lambda _ fun s ↦ measurable_pi_lambda _ fun l ↦ ?_
  have hmean : Measurable (trajEmpiricalMean l s) :=
    (measurable_trajEmpiricalMean l s).mono ((banditFiltration k).le s) le_rfl
  exact hmean.comp (measurable_histExtend n)


/-! ## The rule on histories -/

/-- The arm the rule plays after a history of `n` rounds. -/
noncomputable def safeArmOfHistory [NeZero k] (hk2 : 2 ≤ k) (n : ℕ)
    (h : BanditHistory k n) : Fin k :=
  safeArm hk2 (histMeans n h) n

theorem measurable_safeArmOfHistory [NeZero k] (hk2 : 2 ≤ k) (n : ℕ) :
    Measurable (safeArmOfHistory hk2 n) :=
  (measurable_safeArm hk2 n).comp (measurable_histMeans n)

/-- **Prefix consistency.**  Evaluating the rule on the length-`n` prefix of a
trajectory returns the arm it prescribes at round `n` of that trajectory. -/
theorem safeArmOfHistory_prefix [NeZero k] (hk2 : 2 ≤ k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    safeArmOfHistory hk2 n (banditTrajPrefix k n ω) = safeArm hk2 (trajMeans ω) n := by
  unfold safeArmOfHistory histMeans
  refine safeArm_congr hk2 fun s hs ↦ ?_
  -- the estimates at round `s < n` read only rounds `< s`, all genuine
  funext l
  show trajEmpiricalMean l s (histExtend n (banditTrajPrefix k n ω))
    = trajEmpiricalMean l s ω
  have hagree : ∀ t, t < s → histExtend n (banditTrajPrefix k n ω) t = ω t :=
    fun t ht ↦ histExtend_prefix ω (lt_trans ht hs)
  exact trajEmpiricalMean_congr l s hagree

/-! ## The policy -/

/-- **The sampling rule, as a policy.** -/
noncomputable def safePolicy [NeZero k] (hk2 : 2 ≤ k) : BanditPolicy k where
  select n := Kernel.deterministic (safeArmOfHistory hk2 n)
    (measurable_safeArmOfHistory hk2 n)
  markov n := by infer_instance

theorem safePolicy_select [NeZero k] (hk2 : 2 ≤ k) (n : ℕ) :
    (safePolicy hk2).select n
      = Kernel.deterministic (safeArmOfHistory (k := k) hk2 n)
          (measurable_safeArmOfHistory hk2 n) := rfl

end BanditAlgorithm

/-!
# The trajectory measure realises the rule

The last piece of bookkeeping between the policy of `Solutions/SafePolicy.lean`
and the analysis: almost every trajectory of `banditTrajMeasure ν (safePolicy)`
plays, at every round, the arm the rule prescribes.

The argument is one round at a time.  `banditTrajMeasure_joint_eq_compProd`
identifies the joint law of (prefix of length `n`, round `n`) as
`(law of the prefix) ⊗ₘ (step kernel at n)`, and the step kernel's arm marginal
is `π.select n`, which for this policy is a Dirac mass at the prescribed arm.  So
the set where the played arm differs from the prescribed one is null in the
compProd — fibrewise, by `lintegral_dirac` — and hence null upstairs.  A countable
intersection over `n` gives the statement for all rounds at once.

Note that this is where `∀ ω` becomes `∀ᵐ ω`: a policy cannot constrain
trajectories outside its support, and the trajectory space contains every
sequence.  Statements downstream that were phrased for *every* trajectory have to
be weakened accordingly.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## One round -/

/-- The step kernel of the policy puts no mass on arms other than the prescribed
one. -/
theorem safePolicy_step_arm [NeZero k] (hk2 : 2 ≤ k) (ν : StochasticBandit k)
    (n : ℕ) (h : BanditHistory k n) :
    (banditStepKernel ν (safePolicy hk2) n) h
        {x : Fin k × ℝ | x.1 ≠ safeArmOfHistory hk2 n h} = 0 := by
  classical
  have hmeas : MeasurableSet {x : Fin k × ℝ | x.1 ≠ safeArmOfHistory hk2 n h} := by
    have : {x : Fin k × ℝ | x.1 ≠ safeArmOfHistory hk2 n h}
        = (Prod.fst ⁻¹' {safeArmOfHistory hk2 n h})ᶜ := by
      ext x; simp
    rw [this]
    exact (measurable_fst (measurableSet_singleton _)).compl
  rw [banditStepKernel, Kernel.compProd_apply hmeas, safePolicy_select,
    Kernel.deterministic_apply, lintegral_dirac]
  simp

/-- **Almost surely, round `n` plays the prescribed arm.** -/
theorem safePolicy_ae_arm_eq [NeZero k] (hk2 : 2 ≤ k) (ν : StochasticBandit k)
    (n : ℕ) :
    ∀ᵐ ω ∂(banditTrajMeasure ν (safePolicy hk2)),
      (ω n).1 = safeArmOfHistory hk2 n (banditTrajPrefix k n ω) := by
  classical
  set π : BanditPolicy k := safePolicy hk2 with hπ
  set P : Measure (ℕ → Fin k × ℝ) := banditTrajMeasure ν π with hP
  -- the bad set, upstairs and downstairs
  set B : Set (BanditHistory k n × (Fin k × ℝ)) :=
    {p | p.2.1 ≠ safeArmOfHistory hk2 n p.1} with hB
  have hBmeas : MeasurableSet B := by
    have hfun : Measurable fun p : BanditHistory k n × (Fin k × ℝ) ↦ p.2.1 :=
      measurable_fst.comp measurable_snd
    have hfun' : Measurable fun p : BanditHistory k n × (Fin k × ℝ) ↦
        safeArmOfHistory hk2 n p.1 :=
      (measurable_safeArmOfHistory hk2 n).comp measurable_fst
    exact (measurableSet_eq_fun hfun hfun').compl
  -- it is null in the compProd
  have hnull : (((P.map (banditTrajPrefix k n)) ⊗ₘ (banditStepKernel ν π n)) B) = 0 := by
    rw [Measure.compProd_apply hBmeas]
    have hzero : ∀ h : BanditHistory k n,
        (banditStepKernel ν π n) h (Prod.mk h ⁻¹' B) = 0 := by
      intro h
      have hsec : (Prod.mk h ⁻¹' B) = {x : Fin k × ℝ | x.1 ≠ safeArmOfHistory hk2 n h} := by
        ext x; simp [hB]
      rw [hsec]
      exact safePolicy_step_arm hk2 ν n h
    simp [hzero]
  -- transport it upstairs
  have hjoint := banditTrajMeasure_joint_eq_compProd ν π n
  have hmap : (P.map (fun ω ↦ (banditTrajPrefix k n ω, ω n))) B = 0 := by
    rw [hP, hjoint]; exact hnull
  have hmeasmap : Measurable fun ω : ℕ → Fin k × ℝ ↦ (banditTrajPrefix k n ω, ω n) :=
    (measurable_banditTrajPrefix).prodMk (measurable_pi_apply n)
  rw [Measure.map_apply hmeasmap hBmeas] at hmap
  rw [ae_iff]
  refine measure_mono_null (fun ω hω ↦ ?_) hmap
  exact hω

/-! ## Every round -/

/-- **Almost every trajectory follows the rule.** -/
theorem safePolicy_ae_follows [NeZero k] (hk2 : 2 ≤ k) (ν : StochasticBandit k) :
    ∀ᵐ ω ∂(banditTrajMeasure ν (safePolicy hk2)),
      ∀ n : ℕ, (ω n).1 = safeArm hk2 (trajMeans ω) n := by
  rw [ae_all_iff]
  intro n
  filter_upwards [safePolicy_ae_arm_eq hk2 ν n] with ω hω
  rw [hω, safeArmOfHistory_prefix]

end BanditAlgorithm

/-!
# The trajectory's pull counts are the rule's counts

`safePolicy_ae_follows` says almost every trajectory plays the prescribed arm at
every round.  Since both the trajectory's pull counts and the rule's counts
increment exactly the played arm and start at zero, they agree — by the obvious
induction.

This is the statement the analysis wants: everything proved about
`safeCounts` (the `√(k²+t) − 2k + 1` floor of Lemma 7, the Cesàro limit of
Lemma 8) becomes a statement about `trajPullCount` and hence about
`trajAllocation`, almost surely under the trajectory measure of the policy.

With it, the two guarantees `a2ad182b` needs for its *almost-sure* half are in
place for a concrete policy; what remains for that node is the quantitative half,
the integrability of the settling time.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

variable {k : ℕ}

/-- **A trajectory that follows the rule has the rule's counts.** -/
theorem trajPullCount_eq_safeCounts [NeZero k] (hk2 : 2 ≤ k)
    {ω : ℕ → Fin k × ℝ} (hfollow : ∀ n : ℕ, (ω n).1 = safeArm hk2 (trajMeans ω) n)
    (t : ℕ) (j : Fin k) :
    trajPullCount j t ω = safeCounts hk2 (trajMeans ω) t j := by
  induction t with
  | zero => simp [trajPullCount, safeCounts]
  | succ t ih =>
      rw [trajPullCount_succ, ih, safeCounts, sTrackCounts_succ]
      congr 1
      have hval : (ω t).1 = sTrackArm (safeTarget hk2 (trajMeans ω)) t := hfollow t
      by_cases hj : j = sTrackArm (safeTarget hk2 (trajMeans ω)) t
      · rw [if_pos (hval.trans hj.symm), if_pos hj]
      · exact (if_neg (fun hc ↦ hj (hval.symm.trans hc).symm)).trans (if_neg hj).symm

/-! ## The guarantees, almost surely, for the policy -/

/-- **No arm is starved**, almost surely under the policy. -/
theorem safePolicy_ae_sqrt_le_trajPullCount [NeZero k] (hk2 : 2 ≤ k)
    (ν : StochasticBandit k) :
    ∀ᵐ ω ∂(banditTrajMeasure ν (safePolicy hk2)), ∀ (t : ℕ) (j : Fin k),
      Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) - 2 * (k : ℝ) + 1
        ≤ (trajPullCount j t ω : ℝ) := by
  filter_upwards [safePolicy_ae_follows hk2 ν] with ω hω t j
  rw [trajPullCount_eq_safeCounts hk2 hω t j]
  exact sqrt_le_safeCounts hk2 (trajMeans ω) t j

/-- The weaker form the settling argument consumes. -/
theorem safePolicy_ae_sqrt_sub_le_trajPullCount [NeZero k] (hk2 : 2 ≤ k)
    (ν : StochasticBandit k) :
    ∀ᵐ ω ∂(banditTrajMeasure ν (safePolicy hk2)), ∀ (t : ℕ) (j : Fin k),
      Real.sqrt (t : ℝ) - 2 * (k : ℝ) ≤ (trajPullCount j t ω : ℝ) := by
  filter_upwards [safePolicy_ae_sqrt_le_trajPullCount hk2 ν] with ω hω t j
  have hle : Real.sqrt ((t : ℝ)) ≤ Real.sqrt ((k : ℝ) ^ 2 + (t : ℝ)) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((k : ℝ))])
  have := hω t j
  linarith

end BanditAlgorithm

/-!
# Accurate estimates give accurate targets

The allocation half of Proposition 13 needs to convert "the empirical means are
within `ε` of `μ`" into "the plug-in target is within `ζ` of `α*(μ)`".  That is
continuity of `α*` at `μ`, in `ε`–`δ` form.

**No modulus of continuity is required**, and this is worth stating plainly
because an earlier reading of the problem claimed otherwise.  The window `ζ` is
given first; continuity then supplies *some* `ε`, which is thereafter a fixed
constant, and the probability that the means miss it at round `t` decays like
`e^{−cε²√t}` — fast enough to beat any polynomial weight.  A *rate* for `α*`
would be needed only if `ε` had to shrink with `t`, and it does not.

The second half of the file is the elementary gap between the plug-in allocation
and the target actually tracked: the exploration floor perturbs it by at most
`(k+1)·ε_s`, and `ε_s = 1/(2√(k²+s))` is below any given tolerance from an
explicit round on.  So the tracked target inherits the accuracy of the plug-in
allocation, with a constant delay depending only on `k` and the tolerance.
-/

open Filter Topology Finset Metric

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## Continuity of the measurable selection -/

theorem continuousAt_safeAllocation [NeZero k] (hk2 : 2 ≤ k) {μ : Fin k → ℝ}
    (hμ : μ ∈ StrictBestSet k) : ContinuousAt (safeAllocation hk2) μ := by
  refine (continuousAt_plugInAllocation hk2 hμ).congr ?_
  filter_upwards [isOpen_strictBestSet.mem_nhds hμ] with m hm
  exact (safeAllocation_of_mem hk2 hm).symm

/-- **The `ε`–`ζ` form.**  Given a target accuracy `ζ` for the allocation, some
accuracy `ε` of the means suffices — and `ε` does not depend on the round. -/
theorem exists_eps_of_strict_max [NeZero k] (hk2 : 2 ≤ k) {i : Fin k}
    (hne : (Finset.univ.erase i).Nonempty) {μ : Fin k → ℝ}
    (hμ : ∀ j, j ≠ i → μ j < μ i) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m : Fin k → ℝ, (∀ l, |m l - μ l| ≤ ε) →
      ∀ j, |safeAllocation hk2 m j - optimalAllocation hne μ j| ≤ ζ := by
  have hmem : μ ∈ StrictBestSet k := ⟨i, hμ⟩
  have hcont : ContinuousAt (safeAllocation hk2) μ := continuousAt_safeAllocation hk2 hmem
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ε₀, hε₀, hball⟩ := hcont ζ hζ
  refine ⟨ε₀ / 2, by positivity, fun m hm j ↦ ?_⟩
  have hdist : dist m μ < ε₀ := by
    have hle : dist m μ ≤ ε₀ / 2 := by
      refine (dist_pi_le_iff (by positivity)).mpr fun l ↦ ?_
      rw [Real.dist_eq]
      exact hm l
    linarith
  have hfar := hball hdist
  have hbase : safeAllocation hk2 μ = optimalAllocation hne μ :=
    safeAllocation_eq_of_strict_max hk2 hne hμ
  rw [hbase] at hfar
  have hcoord : dist (safeAllocation hk2 m j) (optimalAllocation hne μ j)
      ≤ dist (safeAllocation hk2 m) (optimalAllocation hne μ) :=
    dist_le_pi_dist _ _ j
  rw [Real.dist_eq] at hcoord
  linarith [le_trans hcoord hfar.le]

/-! ## The exploration floor is eventually negligible -/

/-- Every coordinate of a probability vector is at most one. -/
theorem le_one_of_mem_alloSimplex [NeZero k] {a : Fin k → ℝ}
    (ha : a ∈ alloSimplex k) (j : Fin k) : a j ≤ 1 := by
  classical
  rw [← ha.2]
  exact Finset.single_le_sum (fun l _ ↦ ha.1 l) (Finset.mem_univ j)

/-- **The tracked target is within `(k+1)·ε_s` of the plug-in allocation.** -/
theorem abs_safeTarget_sub_safeAllocation_le [NeZero k] (hk2 : 2 ≤ k)
    (m : ℕ → Fin k → ℝ) (s : ℕ) (j : Fin k) :
    |safeTarget hk2 m s j - safeAllocation hk2 (m s) j|
      ≤ ((k : ℝ) + 1) * exploreFloor k s := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hε : 0 < exploreFloor k s := exploreFloor_pos hk s
  have hnn : 0 ≤ safeAllocation hk2 (m s) j := safeAllocation_nonneg hk2 (m s) j
  have hle1 : safeAllocation hk2 (m s) j ≤ 1 :=
    le_one_of_mem_alloSimplex (safeAllocation_mem hk2 (m s)) j
  have hval : safeTarget hk2 m s j - safeAllocation hk2 (m s) j
      = exploreFloor k s * (1 - (k : ℝ) * safeAllocation hk2 (m s) j) := by
    simp only [safeTarget, flooredTarget, mixUniform]
    ring
  rw [hval, abs_mul, abs_of_pos hε]
  have habs : |1 - (k : ℝ) * safeAllocation hk2 (m s) j| ≤ (k : ℝ) + 1 := by
    rw [abs_le]
    constructor <;> nlinarith [hnn, hle1, hkR]
  calc exploreFloor k s * |1 - (k : ℝ) * safeAllocation hk2 (m s) j|
      ≤ exploreFloor k s * ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left habs hε.le
    _ = ((k : ℝ) + 1) * exploreFloor k s := by ring

/-- The round from which the exploration floor is below `η/(k+1)`. -/
noncomputable def floorRound (k : ℕ) (η : ℝ) : ℕ := ⌈(((k : ℝ) + 1) / (2 * η)) ^ 2⌉₊

theorem exploreFloor_small [NeZero k] {η : ℝ} (hη : 0 < η) {s : ℕ}
    (hs : floorRound k η ≤ s) : ((k : ℝ) + 1) * exploreFloor k s ≤ η := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hthr : (((k : ℝ) + 1) / (2 * η)) ^ 2 ≤ (s : ℝ) := by
    have h1 : ((floorRound k η : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    refine le_trans ?_ h1
    unfold floorRound
    exact Nat.le_ceil _
  have hsum : (((k : ℝ) + 1) / (2 * η)) ^ 2 ≤ (k : ℝ) ^ 2 + (s : ℝ) := by
    nlinarith [sq_nonneg ((k : ℝ))]
  have hsqrt : ((k : ℝ) + 1) / (2 * η) ≤ Real.sqrt ((k : ℝ) ^ 2 + (s : ℝ)) := by
    have hnn : (0 : ℝ) ≤ ((k : ℝ) + 1) / (2 * η) := by positivity
    have h := Real.sqrt_le_sqrt hsum
    rwa [Real.sqrt_sq hnn] at h
  have hpos : (0 : ℝ) < Real.sqrt ((k : ℝ) ^ 2 + (s : ℝ)) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  unfold exploreFloor
  rw [div_le_iff₀ (by positivity)] at hsqrt
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  nlinarith [hsqrt, hpos, hη]

/-- **The tracked target is within `η` of the plug-in allocation from
`floorRound k η` on.** -/
theorem abs_safeTarget_sub_le [NeZero k] (hk2 : 2 ≤ k) (m : ℕ → Fin k → ℝ)
    {η : ℝ} (hη : 0 < η) {s : ℕ} (hs : floorRound k η ≤ s) (j : Fin k) :
    |safeTarget hk2 m s j - safeAllocation hk2 (m s) j| ≤ η :=
  le_trans (abs_safeTarget_sub_safeAllocation_le hk2 m s j) (exploreFloor_small hη hs)

end BanditAlgorithm

/-!
# The Kullback–Leibler divergence between two real Gaussians of equal variance

`D(𝒩(a, v) ‖ 𝒩(b, v)) = (a − b)² / (2v)`.

This is the quantitative input of every fixed-confidence best-arm-identification
bound over the Gaussian class: the characteristic time `c*(ν)` of L&S Eq. (33.4)
is defined through `klDiv`, while the Track-and-Stop statistic `Z_t` is written in
the closed form `½ · T_a T_b/(T_a + T_b) · (μ̂_a − μ̂_b)²`, and the two are related
exactly by this identity.  Mathlib computes the mean and the variance of
`gaussianReal` but not its relative entropy.

The proof is the textbook one.  Both measures have a strictly positive density
against Lebesgue measure, so `d𝒩(a,v)/d𝒩(b,v) = pdf_a / pdf_b` Lebesgue-a.e. and
hence `𝒩(a,v)`-a.e., and the log-likelihood ratio collapses to an *affine*
function of `x`:

  `llr x = ((x − b)² − (x − a)²)/(2v) = (a − b)(2x − a − b)/(2v)`.

Only the first moment of a Gaussian is therefore needed, and `∫ x d𝒩(a,v) = a`
gives `(a − b)(2a − a − b)/(2v) = (a − b)²/(2v)`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {v : ℝ≥0}

theorem nnreal_coe_pos_of_ne_zero (hv : v ≠ 0) : (0 : ℝ) < (v : ℝ) := by
  have : (0 : ℝ≥0) < v := lt_of_le_of_ne bot_le (Ne.symm hv)
  exact_mod_cast this

/-! ## 1. The logarithm of the Gaussian density -/

theorem log_gaussianPDFReal (hv : v ≠ 0) (m x : ℝ) :
    Real.log (gaussianPDFReal m v x)
      = -Real.log (√(2 * π * v)) - (x - m) ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  have hs : (0 : ℝ) < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_inv, Real.log_exp]
  ring

/-- The log-likelihood ratio of two Gaussians with the same variance is affine. -/
theorem log_gaussianPDFReal_sub (hv : v ≠ 0) (a b x : ℝ) :
    Real.log (gaussianPDFReal a v x) - Real.log (gaussianPDFReal b v x)
      = (a - b) * (2 * x - a - b) / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  rw [log_gaussianPDFReal hv, log_gaussianPDFReal hv]
  field_simp
  ring

/-! ## 2. The Radon–Nikodym derivative -/

theorem rnDeriv_gaussianReal_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    (gaussianReal a v).rnDeriv (gaussianReal b v)
      =ᵐ[volume] fun x ↦ (gaussianPDF b v x)⁻¹ * gaussianPDF a v x := by
  have hb : gaussianReal b v = volume.withDensity (gaussianPDF b v) :=
    gaussianReal_of_var_ne_zero _ hv
  have h1 : (gaussianReal a v).rnDeriv (volume.withDensity (gaussianPDF b v))
      =ᵐ[volume] fun x ↦ (gaussianPDF b v x)⁻¹ * (gaussianReal a v).rnDeriv volume x := by
    refine Measure.rnDeriv_withDensity_right _ _ (measurable_gaussianPDF b v).aemeasurable
      (Filter.Eventually.of_forall fun x ↦ (gaussianPDF_pos b hv x).ne')
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [gaussianPDF]
  have h2 : (gaussianReal a v).rnDeriv volume =ᵐ[volume] gaussianPDF a v :=
    rnDeriv_gaussianReal a v
  rw [hb]
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]

/-- The log-likelihood ratio of two same-variance Gaussians, `𝒩(a,v)`-almost
everywhere. -/
theorem llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    llr (gaussianReal a v) (gaussianReal b v)
      =ᵐ[gaussianReal a v] fun x ↦ (a - b) * (2 * x - a - b) / (2 * v) := by
  have hac : gaussianReal a v ≪ volume := gaussianReal_absolutelyContinuous a hv
  have hae : ∀ᵐ x ∂(gaussianReal a v), (gaussianReal a v).rnDeriv (gaussianReal b v) x
      = (gaussianPDF b v x)⁻¹ * gaussianPDF a v x :=
    hac.ae_le (rnDeriv_gaussianReal_gaussianReal hv a b)
  filter_upwards [hae] with x hx
  have hbpos : 0 < gaussianPDFReal b v x := gaussianPDFReal_pos b v x hv
  have hapos : 0 < gaussianPDFReal a v x := gaussianPDFReal_pos a v x hv
  rw [llr, hx, ENNReal.toReal_mul, gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_inv_of_pos hbpos, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hapos.le, Real.log_mul (by positivity) hapos.ne', Real.log_inv,
    ← log_gaussianPDFReal_sub hv a b x]
  ring

/-! ## 3. Integrability and the integral -/

/-- `x ↦ x` is integrable against a Gaussian. -/
theorem integrable_id_gaussianReal (m : ℝ) (w : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x) (gaussianReal m w) := by
  have h : Integrable id (gaussianReal m w) :=
    MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := m) (v := w) 1)
  simpa [Function.id_def] using h

/-- The affine function appearing as the log-likelihood ratio. -/
theorem integrable_llr_form (hv : v ≠ 0) (a b : ℝ) :
    Integrable (fun x : ℝ ↦ (a - b) * (2 * x - a - b) / (2 * v)) (gaussianReal a v) := by
  have hid := integrable_id_gaussianReal a v
  have h1 : Integrable (fun x : ℝ ↦ 2 * x - a - b) (gaussianReal a v) :=
    (((hid.const_mul 2).sub (integrable_const a)).sub (integrable_const b))
  exact (h1.const_mul (a - b)).div_const (2 * v)

theorem integrable_llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    Integrable (llr (gaussianReal a v) (gaussianReal b v)) (gaussianReal a v) :=
  (integrable_llr_form hv a b).congr (llr_gaussianReal hv a b).symm

theorem integral_llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    ∫ x, llr (gaussianReal a v) (gaussianReal b v) x ∂(gaussianReal a v)
      = (a - b) ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  have hid := integrable_id_gaussianReal a v
  rw [integral_congr_ae (llr_gaussianReal hv a b)]
  have hrw : (fun x : ℝ ↦ (a - b) * (2 * x - a - b) / (2 * v))
      = fun x : ℝ ↦ ((a - b) / (v : ℝ)) * x - (a - b) * (a + b) / (2 * v) := by
    funext x
    field_simp
    ring
  rw [hrw, integral_sub (hid.const_mul _) (integrable_const _), integral_const_mul,
    integral_id_gaussianReal]
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul]
  field_simp
  ring

/-! ## 4. The divergence -/

/-- **The Kullback–Leibler divergence between two Gaussians of equal variance.** -/
theorem klDiv_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    klDiv (gaussianReal a v) (gaussianReal b v)
      = ENNReal.ofReal ((a - b) ^ 2 / (2 * v)) := by
  have hac : gaussianReal a v ≪ gaussianReal b v := by
    refine (gaussianReal_absolutelyContinuous a hv).trans ?_
    exact gaussianReal_absolutelyContinuous' b hv
  rw [klDiv_of_ac_of_integrable hac (integrable_llr_gaussianReal hv a b),
    integral_llr_gaussianReal hv a b]
  simp

/-- The unit-variance case, which is the environment class `𝓔^k_𝒩(1)` of L&S
Chapter 33. -/
theorem klDiv_gaussianReal_one (a b : ℝ) :
    klDiv (gaussianReal a 1) (gaussianReal b 1)
      = ENNReal.ofReal ((a - b) ^ 2 / 2) := by
  rw [klDiv_gaussianReal one_ne_zero a b]
  norm_num

end BanditAlgorithm

/-!
# The pooled-mean decomposition

The algebraic identity behind the closed form of the Track-and-Stop statistic
`Z_t` (L&S p. 409).  For weights `p, q ≥ 0` with `p + q > 0` and reals `u, v`,

  `p (u − m)² + q (v − m)² = (p + q)(m − m*)² + pq/(p+q) · (u − v)²`,

where `m* = (pu + qv)/(p + q)` is the pooled mean.  Consequently the left-hand
side is minimised at `m = m*`, with minimum value `pq/(p+q) · (u − v)²`.

In the Gaussian bandit this is exactly the statement that

  `inf_{m} [T_a · D(μ̂_a, m) + T_b · D(μ̂_b, m)] = ½ · T_a T_b/(T_a + T_b) · (μ̂_a − μ̂_b)²`,

since `D(x, m) = (x − m)²/2` for unit-variance Gaussians: the generalised
likelihood ratio for "arm `a` is not better than arm `b`" collapses to the closed
form used by `trajPairGLR`.
-/

namespace BanditAlgorithm

/-- **Pooled-mean decomposition.** -/
theorem weighted_sq_dist_decomp {p q u v m : ℝ} (hpq : p + q ≠ 0) :
    p * (u - m) ^ 2 + q * (v - m) ^ 2
      = (p + q) * (m - (p * u + q * v) / (p + q)) ^ 2 + p * q / (p + q) * (u - v) ^ 2 := by
  field_simp
  ring

/-- The pooled mean minimises the weighted sum of squared distances. -/
theorem pq_mul_sq_sub_le {p q u v m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    p * q / (p + q) * (u - v) ^ 2 ≤ p * (u - m) ^ 2 + q * (v - m) ^ 2 := by
  rw [weighted_sq_dist_decomp hpq.ne']
  have : 0 ≤ (p + q) * (m - (p * u + q * v) / (p + q)) ^ 2 :=
    mul_nonneg hpq.le (sq_nonneg _)
  linarith

/-- Equality is attained at the pooled mean. -/
theorem pq_mul_sq_sub_eq {p q u v : ℝ} (hpq : p + q ≠ 0) :
    p * (u - (p * u + q * v) / (p + q)) ^ 2 + q * (v - (p * u + q * v) / (p + q)) ^ 2
      = p * q / (p + q) * (u - v) ^ 2 := by
  rw [weighted_sq_dist_decomp hpq]
  simp

/-- The minimum over `m` of the weighted sum of squared distances is exactly the
pooled term. -/
theorem iInf_weighted_sq_dist {p q u v : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    ⨅ m : ℝ, (p * (u - m) ^ 2 + q * (v - m) ^ 2) = p * q / (p + q) * (u - v) ^ 2 := by
  have hbdd : BddBelow (Set.range fun m : ℝ ↦ p * (u - m) ^ 2 + q * (v - m) ^ 2) :=
    ⟨p * q / (p + q) * (u - v) ^ 2, by
      rintro _ ⟨m, rfl⟩
      exact pq_mul_sq_sub_le hp hq hpq⟩
  refine le_antisymm ?_ (le_ciInf fun m ↦ pq_mul_sq_sub_le hp hq hpq)
  exact le_of_le_of_eq (ciInf_le hbdd ((p * u + q * v) / (p + q))) (pq_mul_sq_sub_eq hpq.ne')

/-- Half the pooled term, in the form used by `trajPairGLR`. -/
theorem half_pq_mul_sq_sub_le {p q u v m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    p * q / (p + q) * (u - v) ^ 2 / 2
      ≤ p * ((u - m) ^ 2 / 2) + q * ((v - m) ^ 2 / 2) := by
  have h := pq_mul_sq_sub_le hp hq hpq (u := u) (v := v) (m := m)
  linarith

end BanditAlgorithm

/-!
# The Gaussian bandit class `𝓔^k_𝒩(1)`, explicitly

Everything the fixed-confidence analysis needs about `gaussianBandit μ`, made
computable:

* `banditArmMean_gaussianBandit` — the arm means are the parameters;
* `banditOptimalMean_gaussianBandit`, `banditOptimalArms_gaussianBandit` — the
  optimal value and the optimal-arm set are the maximum and the argmax of `μ`;
* `klDiv_gaussianBandit` — `D(ν_i ‖ ν'_i) = (μ_i − μ'_i)²/2`;
* `baiAlternatives_gaussianBandit` — membership in `𝓔_alt(ν)` is a condition on
  the parameter vectors only;
* `baiComplexity_inner_gaussianBandit` — the inner sum defining `c*(ν)⁻¹` is
  `∑_i α_i (μ_i − μ'_i)²/2`.

The last three are what turn the abstract characteristic time of L&S Eq. (33.4)
into the quantity Track-and-Stop actually tracks, and `pooled_pair_glr` is the
bridge to the closed form `trajPairGLR` used by `trajGLR`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Means, optimal value, optimal arms -/

@[simp]
theorem banditArmMean_gaussianBandit (μvec : Fin k → ℝ) (i : Fin k) :
    banditArmMean (gaussianBandit μvec) i = μvec i := by
  simp [banditArmMean, gaussianBandit, integral_id_gaussianReal]

@[simp]
theorem banditOptimalMean_gaussianBandit (μvec : Fin k → ℝ) :
    banditOptimalMean (gaussianBandit μvec) = ⨆ i, μvec i := by
  simp [banditOptimalMean]

@[simp]
theorem banditGap_gaussianBandit (μvec : Fin k → ℝ) (i : Fin k) :
    banditGap (gaussianBandit μvec) i = (⨆ j, μvec j) - μvec i := by
  simp [banditGap]

theorem banditOptimalArms_gaussianBandit (μvec : Fin k → ℝ) :
    banditOptimalArms (gaussianBandit μvec) = {i | μvec i = ⨆ j, μvec j} := by
  ext i
  simp [banditOptimalArms]

/-- With finitely many arms and at least one, the optimal mean is attained. -/
theorem exists_mem_banditOptimalArms [NeZero k] (μvec : Fin k → ℝ) :
    ∃ i, i ∈ banditOptimalArms (gaussianBandit μvec) := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k)) μvec
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  rw [banditOptimalArms_gaussianBandit]
  refine le_antisymm (le_ciSup (f := μvec) (Finite.bddAbove_range _) i) ?_
  exact ciSup_le fun j ↦ hi j (Finset.mem_univ j)

/-- An arm is optimal exactly when it maximises the parameter vector. -/
theorem mem_banditOptimalArms_gaussianBandit_iff [NeZero k] (μvec : Fin k → ℝ) (i : Fin k) :
    i ∈ banditOptimalArms (gaussianBandit μvec) ↔ ∀ j, μvec j ≤ μvec i := by
  rw [banditOptimalArms_gaussianBandit]
  constructor
  · intro hi j
    rw [Set.mem_setOf_eq] at hi
    exact hi ▸ le_ciSup (f := μvec) (Finite.bddAbove_range _) j
  · intro hi
    exact le_antisymm (le_ciSup (f := μvec) (Finite.bddAbove_range _) i) (ciSup_le hi)

/-- The gap is positive exactly when the arm is not optimal. -/
theorem banditGap_pos_iff [NeZero k] (μvec : Fin k → ℝ) (i : Fin k) :
    0 < banditGap (gaussianBandit μvec) i ↔ ∃ j, μvec i < μvec j := by
  rw [banditGap_gaussianBandit, sub_pos]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact absurd (ciSup_le hcon) (not_le.mpr h)
  · rintro ⟨j, hj⟩
    exact lt_of_lt_of_le hj (le_ciSup (f := μvec) (Finite.bddAbove_range _) j)

/-! ## 2. Divergences -/

@[simp]
theorem klDiv_gaussianBandit (a b : Fin k → ℝ) (i : Fin k) :
    klDiv ((gaussianBandit a).P i) ((gaussianBandit b).P i)
      = ENNReal.ofReal ((a i - b i) ^ 2 / 2) := by
  simpa [gaussianBandit] using klDiv_gaussianReal_one (a i) (b i)

/-- The inner sum in the definition of the characteristic time, for Gaussians. -/
theorem baiComplexity_inner_gaussianBandit (a b : Fin k → ℝ) (α : Fin k → ℝ≥0) :
    (∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit a).P i) ((gaussianBandit b).P i))
      = ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((a i - b i) ^ 2 / 2) := by
  simp

/-- The alternative set of a Gaussian bandit inside the Gaussian class, in terms
of the parameter vectors. -/
theorem mem_baiAlternatives_gaussianBandit_iff (a : Fin k → ℝ)
    (ν' : StochasticBandit k) :
    ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit a) ↔
      ∃ b : Fin k → ℝ, ν' = gaussianBandit b ∧
        Disjoint (banditOptimalArms (gaussianBandit b))
          (banditOptimalArms (gaussianBandit a)) := by
  constructor
  · rintro ⟨⟨b, rfl⟩, hdisj⟩
    exact ⟨b, rfl, hdisj⟩
  · rintro ⟨b, rfl, hdisj⟩
    exact ⟨⟨b, rfl⟩, hdisj⟩

/-! ## 3. The bridge to the closed-form pair statistic -/

/-- **The Gaussian generalised likelihood ratio for a pair of arms.**  For weights
`p, q ≥ 0` (the pull counts) the least total divergence achievable by moving both
empirical means to a common value `m` is exactly the closed form used by
`trajPairGLR`. -/
theorem pooled_pair_glr {p q u w : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    ⨅ m : ℝ, (p * ((u - m) ^ 2 / 2) + q * ((w - m) ^ 2 / 2))
      = p * q / (p + q) * (u - w) ^ 2 / 2 := by
  have hbdd : BddBelow (Set.range fun m : ℝ ↦ p * ((u - m) ^ 2 / 2) + q * ((w - m) ^ 2 / 2)) :=
    ⟨p * q / (p + q) * (u - w) ^ 2 / 2, by
      rintro _ ⟨m, rfl⟩
      exact half_pq_mul_sq_sub_le hp hq hpq⟩
  refine le_antisymm ?_ (le_ciInf fun m ↦ half_pq_mul_sq_sub_le hp hq hpq)
  refine le_of_le_of_eq (ciInf_le hbdd ((p * u + q * w) / (p + q))) ?_
  have h := pq_mul_sq_sub_eq (p := p) (q := q) (u := u) (v := w) hpq.ne'
  linarith

/-- The pair statistic of `Def_TrackAndStop` is the Gaussian GLR of the pair. -/
theorem trajPairGLR_eq_iInf (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : 0 < (trajPullCount a t ω : ℝ) + (trajPullCount b t ω : ℝ)) :
    trajPairGLR a b t ω
      = ⨅ m : ℝ, ((trajPullCount a t ω : ℝ) * ((trajEmpiricalMean a t ω - m) ^ 2 / 2)
          + (trajPullCount b t ω : ℝ) * ((trajEmpiricalMean b t ω - m) ^ 2 / 2)) := by
  rw [pooled_pair_glr (Nat.cast_nonneg _) (Nat.cast_nonneg _) h]
  rfl

end BanditAlgorithm

/-!
# The characteristic time of a Gaussian bandit, in closed form

For a Gaussian bandit `ν = ν_μ` with a *unique* best arm `i*` and an allocation
`α` with all weights positive, the inner infimum defining `c*(ν)⁻¹` in
L&S Eq. (33.4) is

  `⨅_{ν' ∈ 𝓔_alt(ν)} ∑_i α_i D(ν_i ‖ ν'_i)
      = min_{j ≠ i*} ½ · α_{i*} α_j / (α_{i*} + α_j) · (μ_{i*} − μ_j)²`.

This is *the* formula of the fixed-confidence literature (Garivier–Kaufmann,
COLT 2016, Eq. (3); L&S Eq. (33.4) specialised to `𝓔^k_𝒩(1)`), and it is what
turns the abstract characteristic time into something an algorithm can track.

Both halves come from the pooled-mean decomposition:

* **Lower bound.**  An alternative must make some arm `j ≠ i*` at least as good
  as `i*`, i.e. `μ'_{i*} ≤ μ'_j`.  Writing `a = μ_{i*} − μ'_{i*}` and
  `b = μ'_j − μ_j`, Cauchy–Schwarz gives
  `p a² + q b² ≥ pq/(p+q) (a + b)²`, and `a + b ≥ μ_{i*} − μ_j ≥ 0`.
* **Upper bound.**  Push `μ_{i*}` down to `m − η` and `μ_j` up to `m + η`, where
  `m` is the pooled mean, leaving every other arm alone.  The resulting bandit is
  a legitimate alternative for every `η > 0`, and its cost exceeds the pooled
  value by `2η pq(μ_{i*} − μ_j)/(p+q) + (p+q)η²/2`, which tends to `0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. The two real-analytic cores -/

/-- **Lower bound.**  If the alternative reverses the order of the pair, its cost
is at least the pooled value. -/
theorem pooled_le_of_crossed {p q u v x y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (huv : v ≤ u) (hxy : x ≤ y) :
    p * q / (p + q) * (u - v) ^ 2 / 2 ≤ p * ((u - x) ^ 2 / 2) + q * ((v - y) ^ 2 / 2) := by
  have hpq : 0 < p + q := by linarith
  set a : ℝ := u - x with ha
  set b : ℝ := y - v with hb
  have hab : u - v ≤ a + b := by simp only [ha, hb]; linarith
  have huv0 : 0 ≤ u - v := by linarith
  -- Cauchy-Schwarz: `p a² + q b² ≥ pq/(p+q) (a+b)²`
  have hcs : p * q / (p + q) * (a + b) ^ 2 ≤ p * a ^ 2 + q * b ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpq]
    nlinarith [sq_nonneg (q * b - p * a), sq_nonneg (a - b)]
  have hsq : (u - v) ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  have hyv : (v - y) ^ 2 = b ^ 2 := by simp only [hb]; ring
  calc p * q / (p + q) * (u - v) ^ 2 / 2
      ≤ p * q / (p + q) * (a + b) ^ 2 / 2 := by
        have hcoef : 0 ≤ p * q / (p + q) := by positivity
        have := mul_le_mul_of_nonneg_left hsq hcoef
        linarith
    _ ≤ (p * a ^ 2 + q * b ^ 2) / 2 := by linarith
    _ = p * ((u - x) ^ 2 / 2) + q * ((v - y) ^ 2 / 2) := by
        rw [hyv]; simp only [ha]; ring

/-- **Upper bound, exact form.**  Splitting the pair symmetrically around the
pooled mean by `η` costs the pooled value plus an explicit `O(η)` term. -/
theorem cost_of_symmetric_split {p q u v η : ℝ} (hpq : p + q ≠ 0) :
    p * ((u - ((p * u + q * v) / (p + q) - η)) ^ 2 / 2)
        + q * ((v - ((p * u + q * v) / (p + q) + η)) ^ 2 / 2)
      = p * q / (p + q) * (u - v) ^ 2 / 2
        + 2 * η * (p * q * (u - v) / (p + q)) + (p + q) * η ^ 2 / 2 := by
  field_simp
  ring

/-! ## 2. The optimal-arm set of a bandit with a unique best arm -/

theorem banditOptimalArms_eq_singleton [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    banditOptimalArms (gaussianBandit μvec) = {istar} := by
  ext i
  rw [mem_banditOptimalArms_gaussianBandit_iff]
  constructor
  · intro hi
    by_contra hne
    exact absurd (hi istar) (not_le.mpr (hstar i hne))
  · intro hi j
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
    rcases eq_or_ne j istar with rfl | hj
    · exact le_rfl
    · exact (hstar j hj).le

/-- Under a unique best arm, being an alternative just means demoting `i*`. -/
theorem mem_baiAlternatives_iff_of_unique [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) (b : Fin k → ℝ) :
    gaussianBandit b ∈ baiAlternatives (Set.range (gaussianBandit (k := k)))
        (gaussianBandit μvec) ↔ ∃ j, b istar < b j := by
  rw [baiAlternatives, Set.mem_setOf_eq, banditOptimalArms_eq_singleton hstar]
  constructor
  · rintro ⟨-, hdisj⟩
    have hnot : istar ∉ banditOptimalArms (gaussianBandit b) := by
      intro hmem
      exact (Set.disjoint_left.mp hdisj hmem) rfl
    rw [mem_banditOptimalArms_gaussianBandit_iff] at hnot
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨⟨b, rfl⟩, ?_⟩
    rw [Set.disjoint_right]
    rintro i rfl
    rw [mem_banditOptimalArms_gaussianBandit_iff]
    intro hcon
    exact absurd (hcon j) (not_le.mpr hj)

/-! ## 3. The formula -/

/-- The pooled cost of the pair `(i*, j)` under the allocation `α`. -/
noncomputable def pairCost (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (istar j : Fin k) : ℝ :=
  (α istar : ℝ) * (α j : ℝ) / ((α istar : ℝ) + (α j : ℝ))
    * (μvec istar - μvec j) ^ 2 / 2

/-- **Lower bound half of the closed form.** -/
theorem le_inner_of_alternative [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hα : ∀ i, 0 < α i) {b : Fin k → ℝ} (hb : ∃ j, b istar < b j) :
    (⨅ j ∈ {j : Fin k | j ≠ istar}, ENNReal.ofReal (pairCost α μvec istar j))
      ≤ ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - b i) ^ 2 / 2) := by
  classical
  obtain ⟨j, hj⟩ := hb
  have hjne : j ≠ istar := by
    rintro rfl
    exact absurd hj (lt_irrefl _)
  have hp : (0 : ℝ) < (α istar : ℝ) := by exact_mod_cast hα istar
  have hq : (0 : ℝ) < (α j : ℝ) := by exact_mod_cast hα j
  -- the cost of the two relevant arms already exceeds the pooled value
  have hcore : ENNReal.ofReal (pairCost α μvec istar j)
      ≤ (α istar : ℝ≥0∞) * ENNReal.ofReal ((μvec istar - b istar) ^ 2 / 2)
        + (α j : ℝ≥0∞) * ENNReal.ofReal ((μvec j - b j) ^ 2 / 2) := by
    have hreal : pairCost α μvec istar j
        ≤ (α istar : ℝ) * ((μvec istar - b istar) ^ 2 / 2)
          + (α j : ℝ) * ((μvec j - b j) ^ 2 / 2) :=
      pooled_le_of_crossed hp hq (hstar j hjne).le hj.le
    calc ENNReal.ofReal (pairCost α μvec istar j)
        ≤ ENNReal.ofReal ((α istar : ℝ) * ((μvec istar - b istar) ^ 2 / 2)
            + (α j : ℝ) * ((μvec j - b j) ^ 2 / 2)) := ENNReal.ofReal_le_ofReal hreal
      _ = (α istar : ℝ≥0∞) * ENNReal.ofReal ((μvec istar - b istar) ^ 2 / 2)
            + (α j : ℝ≥0∞) * ENNReal.ofReal ((μvec j - b j) ^ 2 / 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (le_of_lt hp), ENNReal.ofReal_mul (le_of_lt hq),
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  refine le_trans (iInf_le_of_le j (iInf_le _ hjne)) (le_trans hcore ?_)
  -- and the full sum is at least the two-term sum
  have hsub : ({istar, j} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
  have hpair : (α istar : ℝ≥0∞) * ENNReal.ofReal ((μvec istar - b istar) ^ 2 / 2)
      + (α j : ℝ≥0∞) * ENNReal.ofReal ((μvec j - b j) ^ 2 / 2)
      = ∑ i ∈ ({istar, j} : Finset (Fin k)),
          (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - b i) ^ 2 / 2) := by
    rw [Finset.sum_pair (Ne.symm hjne)]
  rw [hpair]
  exact Finset.sum_le_sum_of_subset hsub

/-! ## 4. Upper bound: the symmetric split is an admissible alternative -/

/-- The alternative that pushes `i*` and `j` symmetrically past each other. -/
noncomputable def splitVec (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (istar j : Fin k)
    (η : ℝ) : Fin k → ℝ := fun l ↦
  if l = istar then
    ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j) / ((α istar : ℝ) + (α j : ℝ)) - η
  else if l = j then
    ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j) / ((α istar : ℝ) + (α j : ℝ)) + η
  else μvec l

/-- The error incurred by the symmetric split. -/
noncomputable def splitError (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (istar j : Fin k)
    (η : ℝ) : ℝ :=
  2 * η * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j) / ((α istar : ℝ) + (α j : ℝ)))
    + ((α istar : ℝ) + (α j : ℝ)) * η ^ 2 / 2

theorem splitError_nonneg {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} {istar j : Fin k} {η : ℝ}
    (hη : 0 ≤ η) (huv : μvec j ≤ μvec istar) : 0 ≤ splitError α μvec istar j η := by
  unfold splitError
  have h1 : 0 ≤ (α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
      / ((α istar : ℝ) + (α j : ℝ)) := by
    apply div_nonneg _ (by positivity)
    have : 0 ≤ μvec istar - μvec j := by linarith
    positivity
  have h2 : 0 ≤ ((α istar : ℝ) + (α j : ℝ)) * η ^ 2 / 2 := by positivity
  have h3 : 0 ≤ 2 * η * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
      / ((α istar : ℝ) + (α j : ℝ))) := by positivity
  linarith

theorem splitError_le {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} {istar j : Fin k} {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (huv : μvec j ≤ μvec istar) :
    splitError α μvec istar j η
      ≤ η * (2 * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
          / ((α istar : ℝ) + (α j : ℝ))) + ((α istar : ℝ) + (α j : ℝ)) / 2) := by
  unfold splitError
  have hC : 0 ≤ (α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
      / ((α istar : ℝ) + (α j : ℝ)) := by
    apply div_nonneg _ (by positivity)
    have : 0 ≤ μvec istar - μvec j := by linarith
    positivity
  have hsq : η ^ 2 ≤ η := by nlinarith
  have hpq : (0 : ℝ) ≤ (α istar : ℝ) + (α j : ℝ) := by positivity
  nlinarith

/-- The cost of the split alternative, exactly. -/
theorem sum_cost_splitVec {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} {istar j : Fin k}
    (hj : j ≠ istar) (hα : ∀ i, 0 < α i) (η : ℝ) (hη : 0 ≤ η)
    (huv : μvec j ≤ μvec istar) :
    (∑ i, (α i : ℝ≥0∞) *
        ENNReal.ofReal ((μvec i - splitVec α μvec istar j η i) ^ 2 / 2))
      = ENNReal.ofReal (pairCost α μvec istar j + splitError α μvec istar j η) := by
  classical
  have hp : (0 : ℝ) < (α istar : ℝ) := by exact_mod_cast hα istar
  have hq : (0 : ℝ) < (α j : ℝ) := by exact_mod_cast hα j
  have hpq : (α istar : ℝ) + (α j : ℝ) ≠ 0 := by positivity
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      i ∉ ({istar, j} : Finset (Fin k)) →
      (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - splitVec α μvec istar j η i) ^ 2 / 2) = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp [splitVec, hi.1, hi.2]
  rw [← Finset.sum_subset (Finset.subset_univ ({istar, j} : Finset (Fin k))) hzero,
    Finset.sum_pair (Ne.symm hj)]
  have hi1 : splitVec α μvec istar j η istar
      = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
          / ((α istar : ℝ) + (α j : ℝ)) - η := by simp [splitVec]
  have hi2 : splitVec α μvec istar j η j
      = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
          / ((α istar : ℝ) + (α j : ℝ)) + η := by simp [splitVec, hj]
  rw [hi1, hi2]
  set m : ℝ := ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
      / ((α istar : ℝ) + (α j : ℝ)) with hm
  set A : ℝ := (μvec istar - (m - η)) ^ 2 / 2 with hA
  set B : ℝ := (μvec j - (m + η)) ^ 2 / 2 with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hlhs : (α istar : ℝ≥0∞) * ENNReal.ofReal A + (α j : ℝ≥0∞) * ENNReal.ofReal B
      = ENNReal.ofReal ((α istar : ℝ) * A + (α j : ℝ) * B) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul hq.le,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  rw [hlhs]
  congr 1
  have hsplit := cost_of_symmetric_split (p := (α istar : ℝ)) (q := (α j : ℝ))
    (u := μvec istar) (v := μvec j) (η := η) hpq
  rw [hA, hB, hm, hsplit]
  unfold pairCost splitError
  ring

theorem pairCost_nonneg {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} (istar j : Fin k) :
    0 ≤ pairCost α μvec istar j := by
  unfold pairCost
  positivity

/-! ## 5. The closed form -/

/-- **The characteristic-time formula for a Gaussian bandit.**  For an allocation
with strictly positive weights and a bandit with a unique best arm, the inner
infimum of L&S Eq. (33.4) is the minimum over the competing arms of the pooled
pair cost. -/
theorem inner_gaussian_eq [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0} (hα : ∀ i, 0 < α i) :
    (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
        ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i))
      = ⨅ j ∈ {j : Fin k | j ≠ istar}, ENNReal.ofReal (pairCost α μvec istar j) := by
  classical
  refine le_antisymm ?_ ?_
  · -- every competing arm gives an admissible alternative, up to `η`
    refine le_iInf₂ fun j hj ↦ ?_
    have hjne : j ≠ istar := hj
    have hp : (0 : ℝ) < (α istar : ℝ) := by exact_mod_cast hα istar
    have hq : (0 : ℝ) < (α j : ℝ) := by exact_mod_cast hα j
    set C : ℝ := 2 * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
        / ((α istar : ℝ) + (α j : ℝ))) + ((α istar : ℝ) + (α j : ℝ)) / 2 with hCdef
    have hC : 0 < C := by
      have h1 : 0 ≤ 2 * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
          / ((α istar : ℝ) + (α j : ℝ))) := by
        have : 0 ≤ μvec istar - μvec j := by linarith [hstar j hjne]
        apply mul_nonneg (by norm_num)
        apply div_nonneg _ (by positivity)
        positivity
      have h2 : 0 < ((α istar : ℝ) + (α j : ℝ)) / 2 := by positivity
      rw [hCdef]; linarith
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    set η : ℝ := min 1 ((ε : ℝ) / C) with hηdef
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hη0 : 0 < η := lt_min one_pos (div_pos hεR hC)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hserr : splitError α μvec istar j η ≤ (ε : ℝ) := by
      calc splitError α μvec istar j η ≤ η * C :=
            splitError_le hη0 hη1 (hstar j hjne).le
        _ ≤ ((ε : ℝ) / C) * C := by
            exact mul_le_mul_of_nonneg_right (min_le_right _ _) hC.le
        _ = (ε : ℝ) := by field_simp
    have hmem : gaussianBandit (splitVec α μvec istar j η)
        ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec) := by
      rw [mem_baiAlternatives_iff_of_unique hstar]
      refine ⟨j, ?_⟩
      have h1 : splitVec α μvec istar j η istar
          = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
              / ((α istar : ℝ) + (α j : ℝ)) - η := by simp [splitVec]
      have h2 : splitVec α μvec istar j η j
          = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
              / ((α istar : ℝ) + (α j : ℝ)) + η := by simp [splitVec, hjne]
      rw [h1, h2]; linarith
    calc (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
            ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i))
        ≤ ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i)
            ((gaussianBandit (splitVec α μvec istar j η)).P i) :=
          iInf₂_le _ hmem
      _ = ∑ i, (α i : ℝ≥0∞) *
            ENNReal.ofReal ((μvec i - splitVec α μvec istar j η i) ^ 2 / 2) := by
          simp
      _ = ENNReal.ofReal (pairCost α μvec istar j + splitError α μvec istar j η) :=
          sum_cost_splitVec hjne hα η hη0.le (hstar j hjne).le
      _ = ENNReal.ofReal (pairCost α μvec istar j)
            + ENNReal.ofReal (splitError α μvec istar j η) :=
          ENNReal.ofReal_add (pairCost_nonneg _ _)
            (splitError_nonneg hη0.le (hstar j hjne).le)
      _ ≤ ENNReal.ofReal (pairCost α μvec istar j) + (ε : ℝ≥0∞) := by
          gcongr
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal hserr
  · -- every alternative costs at least the pooled minimum
    refine le_iInf₂ fun ν' hν' ↦ ?_
    obtain ⟨b, rfl⟩ : ∃ b : Fin k → ℝ, gaussianBandit b = ν' := hν'.1
    have hb : ∃ l, b istar < b l := (mem_baiAlternatives_iff_of_unique hstar b).mp hν'
    have hrw : (∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i)
        ((gaussianBandit b).P i))
        = ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - b i) ^ 2 / 2) := by simp
    rw [hrw]
    exact le_inner_of_alternative hstar hα hb

end BanditAlgorithm

/-!
# The characteristic time of a Gaussian bandit is finite, with an explicit bound

Plugging the *uniform* allocation into the closed form of
`gaussian_bai_characteristic_time_formula` gives

  `c*(ν)⁻¹ ≥ min_{j ≠ i*} Δ_j² / (4k)`,   i.e.   `c*(ν) ≤ 4k / Δ_min²`.

Finiteness is not a technicality: L&S Theorem 33.6 and its lower half both speak
of `c*(ν).toReal`, and `ℝ≥0∞`-to-`ℝ` coercion silently sends `∞` to `0`, so
without `c*(ν) ≠ ∞` the statement of the theorem would be about the wrong
quantity.  The bound `4k/Δ_min²` is the familiar "the harder the gaps, the longer
it takes" scaling, and matches the `H₂`-style complexities of the fixed-budget
chapters.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The uniform allocation. -/
noncomputable def uniformAllocation (k : ℕ) : Fin k → ℝ≥0 := fun _ ↦ (k : ℝ≥0)⁻¹

theorem uniformAllocation_pos (hk : 0 < k) (i : Fin k) : 0 < uniformAllocation k i := by
  have : (0 : ℝ≥0) < (k : ℝ≥0) := by exact_mod_cast hk
  simpa [uniformAllocation] using this

theorem sum_uniformAllocation (hk : 0 < k) : ∑ i, uniformAllocation k i = 1 := by
  have hkne : (k : ℝ≥0) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hk.ne'
  simp only [uniformAllocation, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ hkne

/-- The pair cost of the uniform allocation. -/
theorem pairCost_uniformAllocation (hk : 0 < k) (μvec : Fin k → ℝ) (istar j : Fin k) :
    pairCost (uniformAllocation k) μvec istar j
      = (μvec istar - μvec j) ^ 2 / (4 * (k : ℝ)) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  unfold pairCost uniformAllocation
  have hcast : (((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = ((k : ℝ))⁻¹ := by
    simp
  rw [hcast]
  field_simp
  ring

/-- **The characteristic time is finite.**  Any positive lower bound on the gaps
gives an explicit bound on `c*(ν)`. -/
theorem baiComplexity_le_of_gap_le [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ j, j ≠ istar → Δ ≤ μvec istar - μvec j) :
    baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k)))
      ≤ ENNReal.ofReal (4 * (k : ℝ) / Δ ^ 2) := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- the uniform allocation already achieves `Δ²/(4k)`
  have hval : ENNReal.ofReal (Δ ^ 2 / (4 * (k : ℝ)))
      ≤ ⨅ j ∈ {j : Fin k | j ≠ istar},
          ENNReal.ofReal (pairCost (uniformAllocation k) μvec istar j) := by
    refine le_iInf₂ fun j hj ↦ ?_
    rw [pairCost_uniformAllocation hk]
    refine ENNReal.ofReal_le_ofReal ?_
    have hgj : Δ ≤ μvec istar - μvec j := hgap j hj
    have : Δ ^ 2 ≤ (μvec istar - μvec j) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right this (by positivity) |>.trans_eq rfl
  have hformula := inner_gaussian_eq hstar (uniformAllocation_pos hk)
  have hle : ENNReal.ofReal (Δ ^ 2 / (4 * (k : ℝ)))
      ≤ ⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
          ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
            ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i) := by
    refine le_trans (le_trans hval (le_of_eq hformula.symm)) ?_
    exact le_iSup₂ (f := fun α (_ : α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}) ↦
      ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
        ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i))
      (uniformAllocation k) (sum_uniformAllocation hk)
  rw [baiComplexity]
  refine le_trans (ENNReal.inv_le_inv.mpr hle) (le_of_eq ?_)
  rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp

/-- **Finiteness of the characteristic time.** -/
theorem baiComplexity_ne_top [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k))) ≠ ⊤ := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  by_cases hk1 : ∀ j : Fin k, j = istar
  · -- a single arm: the alternative set is empty, so the infimum is `∞` and `c* = 0`
    have hempty : baiAlternatives (Set.range (gaussianBandit (k := k)))
        (gaussianBandit μvec) = ∅ := by
      ext ν'
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro hν'
      obtain ⟨b, rfl⟩ : ∃ b : Fin k → ℝ, gaussianBandit b = ν' := hν'.1
      obtain ⟨j, hj⟩ := (mem_baiAlternatives_iff_of_unique hstar b).mp hν'
      rw [hk1 j] at hj
      exact absurd hj (lt_irrefl _)
    have : baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k))) = 0 := by
      rw [baiComplexity]
      have htop : (⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
          ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
            ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i)) = ⊤ := by
        refine le_antisymm le_top ?_
        refine le_iSup₂_of_le (uniformAllocation k) (sum_uniformAllocation hk) ?_
        rw [hempty]
        simp
      rw [htop, ENNReal.inv_top]
    rw [this]
    exact ENNReal.zero_ne_top
  · -- at least two arms: use the explicit bound with the smallest gap
    push_neg at hk1
    obtain ⟨j₀, hj₀⟩ := hk1
    set S : Finset (Fin k) := Finset.univ.filter (fun j ↦ j ≠ istar) with hS
    have hSne : S.Nonempty := ⟨j₀, by simp [hS, hj₀]⟩
    set Δ : ℝ := S.inf' hSne (fun j ↦ μvec istar - μvec j) with hΔdef
    have hΔ : 0 < Δ := by
      rw [hΔdef, Finset.lt_inf'_iff]
      intro j hj
      have : j ≠ istar := by simpa [hS] using hj
      linarith [hstar j this]
    have hgap : ∀ j, j ≠ istar → Δ ≤ μvec istar - μvec j := by
      intro j hj
      exact Finset.inf'_le _ (by simp [hS, hj])
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (baiComplexity_le_of_gap_le hstar hΔ hgap)

end BanditAlgorithm

/-!
# Existence of an optimal allocation

L&S Eq. (33.4) defines `c*(ν)⁻¹` as a *supremum* over the simplex.  Track-and-Stop
needs that supremum to be *attained*: the sampling rule tracks a maximiser `α*`.
This file supplies the maximiser for the Gaussian class.

The argument is the standard one, made possible by the closed form
`gaussian_bai_characteristic_time_formula`:

* the objective `α ↦ min_{j ≠ i*} α_{i*} α_j/(α_{i*} + α_j) · Δ_j²/2` is continuous
  on the whole of `Fin k → ℝ≥0` — the only delicate point is the origin of a pair,
  where the squeeze `0 ≤ pq/(p+q) ≤ p` applies;
* the simplex is compact, being a closed subset of the box `[0,1]^k`;
* so the maximum is attained, and the maximiser has full support because the
  objective vanishes as soon as one coordinate does, while the uniform allocation
  already achieves a strictly positive value.

Full support is exactly what lets the closed form be applied at the maximiser, so
the maximiser of the *closed form* is a maximiser of the original `ℝ≥0∞`-valued
objective.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Continuity of the pair fraction -/

/-- `p q / (p + q)` is bounded by `p` on the nonnegative quadrant. -/
theorem pairFrac_le (p q : ℝ≥0) : (p : ℝ) * q / ((p : ℝ) + q) ≤ (p : ℝ) := by
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (p : ℝ) + q) with h | h
  · rw [← h]; simp
  · rw [div_le_iff₀ h]
    nlinarith [q.coe_nonneg, p.coe_nonneg]

theorem pairFrac_nonneg (p q : ℝ≥0) : 0 ≤ (p : ℝ) * q / ((p : ℝ) + q) := by positivity

/-- The pair fraction is continuous on `ℝ≥0 × ℝ≥0`. -/
theorem continuous_pairFrac :
    Continuous fun x : ℝ≥0 × ℝ≥0 ↦ (x.1 : ℝ) * x.2 / ((x.1 : ℝ) + x.2) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (x.1 : ℝ) + x.2) with h | h
  · -- both coordinates vanish: squeeze between `0` and the first coordinate
    have hx1 : (x.1 : ℝ) = 0 := by
      have h1 : (0 : ℝ) ≤ (x.1 : ℝ) := x.1.coe_nonneg
      have h2 : (0 : ℝ) ≤ (x.2 : ℝ) := x.2.coe_nonneg
      linarith
    have hval : (x.1 : ℝ) * x.2 / ((x.1 : ℝ) + x.2) = 0 := by rw [hx1]; simp
    rw [ContinuousAt, hval]
    refine squeeze_zero' (Filter.Eventually.of_forall fun y ↦ pairFrac_nonneg y.1 y.2)
      (Filter.Eventually.of_forall fun y ↦ pairFrac_le y.1 y.2) ?_
    have : Filter.Tendsto (fun y : ℝ≥0 × ℝ≥0 ↦ ((y.1 : ℝ))) (nhds x) (nhds ((x.1 : ℝ))) :=
      (NNReal.continuous_coe.comp continuous_fst).continuousAt
    rw [hx1] at this
    exact this
  · -- the denominator is nonzero
    refine ContinuousAt.div ?_ ?_ (ne_of_gt h)
    · exact ((NNReal.continuous_coe.comp continuous_fst).mul
        (NNReal.continuous_coe.comp continuous_snd)).continuousAt
    · exact ((NNReal.continuous_coe.comp continuous_fst).add
        (NNReal.continuous_coe.comp continuous_snd)).continuousAt

/-- `pairCost` is continuous in the allocation. -/
theorem continuous_pairCost (μvec : Fin k → ℝ) (istar j : Fin k) :
    Continuous fun α : Fin k → ℝ≥0 ↦ pairCost α μvec istar j := by
  unfold pairCost
  have hpair : Continuous fun α : Fin k → ℝ≥0 ↦ ((α istar, α j) : ℝ≥0 × ℝ≥0) :=
    (continuous_apply istar).prodMk (continuous_apply j)
  have h : Continuous fun α : Fin k → ℝ≥0 ↦
      ((α istar : ℝ) * (α j : ℝ) / ((α istar : ℝ) + (α j : ℝ))) :=
    continuous_pairFrac.comp hpair
  exact ((h.mul continuous_const).div_const 2)

/-! ## 2. Compactness of the simplex -/

theorem isCompact_simplex (k : ℕ) :
    IsCompact {α : Fin k → ℝ≥0 | ∑ i, α i = 1} := by
  have hclosed : IsClosed {α : Fin k → ℝ≥0 | ∑ i, α i = 1} := by
    have hcont : Continuous fun α : Fin k → ℝ≥0 ↦ ∑ i, α i :=
      continuous_finset_sum _ fun i _ ↦ continuous_apply i
    exact isClosed_eq hcont continuous_const
  have hsub : {α : Fin k → ℝ≥0 | ∑ i, α i = 1} ⊆ Set.Icc (0 : Fin k → ℝ≥0) 1 := by
    intro α hα
    refine ⟨fun i ↦ zero_le', fun i ↦ ?_⟩
    have : α i ≤ ∑ j, α j := Finset.single_le_sum (fun j _ ↦ zero_le') (Finset.mem_univ i)
    rw [hα] at this
    exact this
  exact IsCompact.of_isClosed_subset (isCompact_Icc) hclosed hsub

theorem simplex_nonempty (hk : 0 < k) :
    {α : Fin k → ℝ≥0 | ∑ i, α i = 1}.Nonempty :=
  ⟨uniformAllocation k, sum_uniformAllocation hk⟩

/-! ## 3. The maximiser -/

/-- The closed-form objective: the smallest pooled pair cost among the competing
arms.  With `Finset.inf'` this needs the competing set to be nonempty, i.e. `k ≥ 2`. -/
noncomputable def allocObjective (μvec : Fin k → ℝ) (istar : Fin k)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    (α : Fin k → ℝ≥0) : ℝ :=
  (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).inf' hne fun j ↦ pairCost α μvec istar j

theorem continuous_allocObjective (μvec : Fin k → ℝ) (istar : Fin k)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty) :
    Continuous (allocObjective μvec istar hne) := by
  rw [continuous_iff_continuousAt]
  intro α
  unfold allocObjective ContinuousAt
  exact Filter.Tendsto.finset_inf'_nhds_apply hne fun j _ ↦
    (continuous_pairCost μvec istar j).continuousAt

/-- **A maximiser exists.** -/
theorem exists_max_allocObjective (hk : 0 < k) (μvec : Fin k → ℝ) (istar : Fin k)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty) :
    ∃ α₀ ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
      ∀ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
        allocObjective μvec istar hne α ≤ allocObjective μvec istar hne α₀ := by
  obtain ⟨α₀, hα₀, hmax⟩ := (isCompact_simplex k).exists_isMaxOn (simplex_nonempty hk)
    (continuous_allocObjective μvec istar hne).continuousOn
  exact ⟨α₀, hα₀, fun α hα ↦ hmax hα⟩

/-! ## 4. The maximiser has full support -/

theorem allocObjective_uniform_pos (hk : 0 < k) {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty) :
    0 < allocObjective μvec istar hne (uniformAllocation k) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [allocObjective, Finset.lt_inf'_iff]
  intro j hj
  have hjne : j ≠ istar := by simpa using hj
  rw [pairCost_uniformAllocation hk]
  have hgap : 0 < μvec istar - μvec j := by linarith [hstar j hjne]
  positivity

theorem pairCost_eq_zero_of_coord_eq_zero {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ}
    {istar j : Fin k} (h : α istar = 0 ∨ α j = 0) :
    pairCost α μvec istar j = 0 := by
  unfold pairCost
  rcases h with h | h <;> simp [h]

/-- A maximiser of the objective has all coordinates positive. -/
theorem pos_of_isMax (hk : 0 < k) {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    {α₀ : Fin k → ℝ≥0} (hα₀ : ∑ i, α₀ i = 1)
    (hmax : ∀ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
      allocObjective μvec istar hne α ≤ allocObjective μvec istar hne α₀) :
    ∀ i, 0 < α₀ i := by
  have hpos : 0 < allocObjective μvec istar hne α₀ :=
    lt_of_lt_of_le (allocObjective_uniform_pos hk hstar hne)
      (hmax _ (sum_uniformAllocation hk))
  intro i
  rcases eq_or_lt_of_le (zero_le' : (0 : ℝ≥0) ≤ α₀ i) with h | h
  · exfalso
    -- a vanishing coordinate makes some pair cost vanish
    rcases eq_or_ne i istar with hi | hi
    · obtain ⟨j, hj⟩ := id hne
      have hle : allocObjective μvec istar hne α₀ ≤ pairCost α₀ μvec istar j :=
        Finset.inf'_le _ hj
      rw [pairCost_eq_zero_of_coord_eq_zero (Or.inl (hi ▸ h.symm))] at hle
      linarith
    · have hmem : i ∈ Finset.univ.filter fun j : Fin k ↦ j ≠ istar := by simp [hi]
      have hle : allocObjective μvec istar hne α₀ ≤ pairCost α₀ μvec istar i :=
        Finset.inf'_le _ hmem
      rw [pairCost_eq_zero_of_coord_eq_zero (Or.inr h.symm)] at hle
      linarith
  · exact h

/-! ## 5. Degenerate allocations cost nothing -/

/-- An `ℝ≥0∞` infimum of `ofReal`s over a nonempty finite set is the `ofReal` of the
`Finset.inf'`. -/
theorem iInf_ofReal_eq_ofReal_inf' {S : Finset (Fin k)} (hne : S.Nonempty)
    (f : Fin k → ℝ) (hf : ∀ j ∈ S, 0 ≤ f j) :
    (⨅ j ∈ (↑S : Set (Fin k)), ENNReal.ofReal (f j)) = ENNReal.ofReal (S.inf' hne f) := by
  refine le_antisymm ?_ (le_iInf₂ fun j hj ↦ ENNReal.ofReal_le_ofReal (Finset.inf'_le _ hj))
  obtain ⟨j₀, hj₀S, hj₀⟩ := Finset.exists_mem_eq_inf' hne f
  exact le_trans (iInf_le_of_le j₀ (iInf_le _ hj₀S)) (le_of_eq (by rw [hj₀]))

/-- If some weight vanishes, the alternative set contains a bandit of zero cost. -/
theorem inner_eq_zero_of_coord_eq_zero [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {β : Fin k → ℝ≥0} {i : Fin k}
    (hi : β i = 0) (j₀ : Fin k) (hj₀ : j₀ ≠ istar) :
    (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
        ∑ l, (β l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l) (ν'.P l)) = 0 := by
  classical
  refine le_antisymm ?_ bot_le
  set c : ℝ := if i = istar then μvec j₀ - 1 else μvec istar + 1 with hc
  set b : Fin k → ℝ := fun l ↦ if l = i then c else μvec l with hb
  have hbi : b i = c := by rw [hb]; simp
  have hbne : ∀ l, l ≠ i → b l = μvec l := by
    intro l hl; rw [hb]; simp [hl]
  have hmem : gaussianBandit b ∈ baiAlternatives
      (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec) := by
    rw [mem_baiAlternatives_iff_of_unique hstar]
    rcases eq_or_ne i istar with hii | hii
    · refine ⟨j₀, ?_⟩
      have hji : j₀ ≠ i := by rw [hii]; exact hj₀
      have h1 : b istar = μvec j₀ - 1 := by
        rw [← hii, hbi, hc, if_pos hii]
      have h2 : b j₀ = μvec j₀ := hbne j₀ hji
      rw [h1, h2]; linarith
    · refine ⟨i, ?_⟩
      have h1 : b istar = μvec istar := hbne istar (Ne.symm hii)
      have h2 : b i = μvec istar + 1 := by rw [hbi, hc, if_neg hii]
      rw [h1, h2]; linarith
  have hcost : (∑ l, (β l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l)
      ((gaussianBandit b).P l)) = 0 := by
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    rcases eq_or_ne l i with rfl | hli
    · rw [hi]; simp
    · rw [klDiv_gaussianBandit, hbne l hli]; simp
  exact le_trans (iInf₂_le _ hmem) (le_of_eq hcost)

/-! ## 6. Existence of an optimal allocation -/

/-- **An optimal allocation exists, and it has full support.** -/
theorem exists_isOptimalAllocation [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    ∃ α : Fin k → ℝ≥0, (∀ i, 0 < α i) ∧
      IsOptimalAllocation (gaussianBandit μvec)
        (Set.range (gaussianBandit (k := k))) α := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  set S : Finset (Fin k) := Finset.univ.filter (fun j : Fin k ↦ j ≠ istar) with hS
  have hinv : (baiComplexity (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))))⁻¹
      = ⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
          ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k)))
              (gaussianBandit μvec),
            ∑ l, (α l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l) (ν'.P l) := by
    rw [baiComplexity, inv_inv]
  rcases S.eq_empty_or_nonempty with hSe | hne
  · refine ⟨uniformAllocation k, uniformAllocation_pos hk, sum_uniformAllocation hk, ?_⟩
    have hempty : baiAlternatives (Set.range (gaussianBandit (k := k)))
        (gaussianBandit μvec) = ∅ := by
      ext ν'
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro hν'
      obtain ⟨c, rfl⟩ : ∃ c : Fin k → ℝ, gaussianBandit c = ν' := hν'.1
      obtain ⟨j, hj⟩ := (mem_baiAlternatives_iff_of_unique hstar c).mp hν'
      have hjs : j = istar := by
        by_contra hcon
        have hmemS : j ∈ S := by simp [hS, hcon]
        rw [hSe] at hmemS
        exact absurd hmemS (Finset.notMem_empty j)
      rw [hjs] at hj
      exact absurd hj (lt_irrefl _)
    rw [hinv, hempty]
    simp only [Set.mem_empty_iff_false, iInf_false, iInf_top]
    symm
    refine le_antisymm le_top ?_
    exact le_iSup₂_of_le (f := fun (α : Fin k → ℝ≥0)
      (_ : α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}) ↦ (⊤ : ℝ≥0∞))
      (uniformAllocation k) (sum_uniformAllocation hk) le_rfl
  · obtain ⟨j₀, hj₀mem⟩ := id hne
    have hj₀ne : j₀ ≠ istar := by simpa [hS] using hj₀mem
    obtain ⟨α₀, hα₀mem, hα₀max⟩ := exists_max_allocObjective hk μvec istar hne
    have hα₀sum : ∑ i, α₀ i = 1 := hα₀mem
    have hα₀pos := pos_of_isMax hk hstar hne hα₀sum hα₀max
    have hFfull : ∀ α : Fin k → ℝ≥0, (∀ i, 0 < α i) →
        (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k)))
            (gaussianBandit μvec),
          ∑ l, (α l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l) (ν'.P l))
          = ENNReal.ofReal (allocObjective μvec istar hne α) := by
      intro α hα
      rw [inner_gaussian_eq hstar hα]
      have hsets : {j : Fin k | j ≠ istar} = (↑S : Set (Fin k)) := by
        ext j; simp [hS]
      rw [hsets]
      exact iInf_ofReal_eq_ofReal_inf' hne _ fun j _ ↦ pairCost_nonneg _ _
    refine ⟨α₀, hα₀pos, hα₀sum, ?_⟩
    rw [hinv]
    refine le_antisymm (le_iSup₂ (f := fun (α : Fin k → ℝ≥0)
      (_ : α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}) ↦
        ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
          ∑ l, (α l : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P l) (ν'.P l))
      α₀ hα₀mem) ?_
    refine iSup₂_le fun β hβ ↦ ?_
    by_cases hfull : ∀ i, 0 < β i
    · rw [hFfull β hfull, hFfull α₀ hα₀pos]
      exact ENNReal.ofReal_le_ofReal (hα₀max β hβ)
    · push_neg at hfull
      obtain ⟨i, hi⟩ := hfull
      have hzero : β i = 0 := le_antisymm hi zero_le'
      rw [inner_eq_zero_of_coord_eq_zero hstar hzero j₀ hj₀ne]
      exact bot_le

end BanditAlgorithm

/-!
# The platform-level statement: `IsOptimalAllocation` determines the allocation

`Solutions/AllocationUnique.lean` proves uniqueness for the closed-form objective
`Ψ_i(μ, α) = min_{j ≠ i} α_i α_j/(α_i + α_j) · (μ_i − μ_j)²/2`.  The
Track-and-Stop development states optimality instead through
`IsOptimalAllocation`, the definition of Lattimore & Szepesvári Eq. (33.4):

  `∑_i α_i = 1`  and  `⨅_{ν' ∈ 𝓔_alt(ν)} ∑_i α_i · D(ν_i, ν'_i) = c*(ν)⁻¹`.

This file connects the two and transports uniqueness across, giving

  **`isOptimalAllocation_unique`**: for a Gaussian bandit with a strictly best
  arm, any two optimal allocations are equal.

## The three links

*From the variational form to the closed form.*  `inner_gaussian_eq`
(`Solutions/GaussianComplexity.lean`) evaluates the inner infimum for a
full-support allocation as `⨅_{j ≠ i} ofReal(pairCost)`, and
`iInf_ofReal_eq_ofReal_inf'` turns that `ℝ≥0∞` infimum into `ofReal` of a
`Finset.inf'`.  So on full-support allocations the platform's objective is
`ENNReal.ofReal` of the closed-form one.

*From "attains `c*(ν)⁻¹`" to "is a maximiser".*  `c*(ν)⁻¹` is by definition the
supremum of the inner infimum over the simplex, so an allocation attains it
exactly when it dominates every other allocation — this is `isOptimalAllocation_iff`,
and it is pure `ℝ≥0∞` lattice manipulation.

*Degenerate allocations are not maximisers.*  A vanishing weight makes the inner
infimum `0` (`inner_eq_zero_of_coord_eq_zero`), while the uniform allocation
achieves a positive value, so every optimal allocation has full support and the
previous two links apply to it.

The one place to be careful is that `ENNReal.ofReal` is monotone but not
injective on all of `ℝ` — it collapses the negatives.  Every value in sight is
nonnegative (`pairCost` is a product of nonnegative factors), so on the range
that occurs it *is* injective, and the comparison transfers in both directions.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter Finset

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The two index sets agree -/

theorem erase_eq_filter_ne (istar : Fin k) :
    Finset.univ.erase istar = Finset.univ.filter (fun j : Fin k ↦ j ≠ istar) := by
  ext j
  simp

/-- The closed-form objective of `Solutions/AllocationObjective.lean` is the
objective of `Solutions/OptimalAllocation.lean`, on the nonnegative reals. -/
theorem alloRate_eq_allocObjective {istar : Fin k}
    (hne : (Finset.univ.erase istar).Nonempty)
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    (μvec : Fin k → ℝ) (α : Fin k → ℝ≥0) :
    alloRate hne μvec (fun j ↦ (α j : ℝ)) = allocObjective μvec istar hne' α := by
  unfold alloRate allocObjective
  refine Finset.inf'_congr hne (erase_eq_filter_ne istar) fun j _ ↦ ?_
  unfold harmCost pairHarm pairCost
  ring

/-! ## Attaining `c*(ν)⁻¹` means dominating every allocation -/

/-- The inner infimum of Eq. (33.4) at an allocation. -/
noncomputable def innerInf (μvec : Fin k → ℝ) (α : Fin k → ℝ≥0) : ℝ≥0∞ :=
  ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
    ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i)

theorem baiComplexity_inv_eq (μvec : Fin k → ℝ) :
    (baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k))))⁻¹
      = ⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}, innerInf μvec α := by
  rw [baiComplexity, inv_inv]
  rfl

/-- **Optimality is maximality.**  An allocation attains `c*(ν)⁻¹` exactly when no
allocation does better. -/
theorem isOptimalAllocation_iff (μvec : Fin k → ℝ) (α : Fin k → ℝ≥0) :
    IsOptimalAllocation (gaussianBandit μvec)
        (Set.range (gaussianBandit (k := k))) α
      ↔ (∑ i, α i = 1) ∧
        ∀ β : Fin k → ℝ≥0, ∑ i, β i = 1 → innerInf μvec β ≤ innerInf μvec α := by
  unfold IsOptimalAllocation
  rw [baiComplexity_inv_eq]
  constructor
  · rintro ⟨hsum, hattain⟩
    refine ⟨hsum, fun β hβ ↦ ?_⟩
    rw [show innerInf μvec α = _ from hattain]
    exact le_iSup₂ (f := fun β (_ : β ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}) ↦
      innerInf μvec β) β hβ
  · rintro ⟨hsum, hdom⟩
    refine ⟨hsum, le_antisymm ?_ ?_⟩
    · exact le_iSup₂ (f := fun β (_ : β ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}) ↦
        innerInf μvec β) α hsum
    · exact iSup₂_le fun β hβ ↦ hdom β hβ

/-! ## Optimal allocations have full support -/

theorem innerInf_eq_ofReal [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    {α : Fin k → ℝ≥0} (hα : ∀ i, 0 < α i) :
    innerInf μvec α = ENNReal.ofReal (allocObjective μvec istar hne' α) := by
  classical
  rw [innerInf, inner_gaussian_eq hstar hα]
  have hset : {j : Fin k | j ≠ istar}
      = (↑(Finset.univ.filter fun j : Fin k ↦ j ≠ istar) : Set (Fin k)) := by
    ext j; simp
  rw [hset]
  exact iInf_ofReal_eq_ofReal_inf' hne' _ fun j _ ↦ pairCost_nonneg istar j

/-- **Every optimal allocation has full support.** -/
theorem pos_of_isOptimalAllocation [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hα : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) α) (i : Fin k) : 0 < α i := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  rw [isOptimalAllocation_iff] at hα
  obtain ⟨hsum, hdom⟩ := hα
  rcases (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).eq_empty_or_nonempty with
    hSe | hne'
  · -- no competing arm: `istar` is the only arm, so it carries all the mass
    have hall : ∀ j : Fin k, j = istar := by
      intro j
      by_contra hj
      have hmem : j ∈ Finset.univ.filter fun l : Fin k ↦ l ≠ istar := by simp [hj]
      rw [hSe] at hmem
      exact absurd hmem (Finset.notMem_empty j)
    have hsingle : ∑ l : Fin k, α l = α istar :=
      Finset.sum_eq_single istar (fun l _ hl ↦ absurd (hall l) hl)
        (fun h ↦ absurd (Finset.mem_univ istar) h)
    have hone : α istar = 1 := by rw [← hsingle, hsum]
    rw [hall i, hone]
    norm_num
  · by_contra hcon
    push_neg at hcon
    have hzero : α i = 0 := le_antisymm hcon (zero_le' )
    obtain ⟨j₀, hj₀⟩ := id hne'
    have hj₀ne : j₀ ≠ istar := by simpa using hj₀
    have hzeroInf : innerInf μvec α = 0 :=
      inner_eq_zero_of_coord_eq_zero hstar hzero j₀ hj₀ne
    -- the uniform allocation does strictly better
    have huni : innerInf μvec (uniformAllocation k)
        = ENNReal.ofReal (allocObjective μvec istar hne' (uniformAllocation k)) :=
      innerInf_eq_ofReal hstar hne' (uniformAllocation_pos hk)
    have hpos : 0 < allocObjective μvec istar hne' (uniformAllocation k) :=
      allocObjective_uniform_pos hk hstar hne'
    have hle := hdom (uniformAllocation k) (sum_uniformAllocation hk)
    rw [hzeroInf, huni] at hle
    have : (0 : ℝ≥0∞) < ENNReal.ofReal (allocObjective μvec istar hne' (uniformAllocation k)) :=
      ENNReal.ofReal_pos.mpr hpos
    exact absurd hle (not_le.mpr this)

theorem allocObjective_nonneg {μvec : Fin k → ℝ} {istar : Fin k}
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    (γ : Fin k → ℝ≥0) : 0 ≤ allocObjective μvec istar hne' γ := by
  unfold allocObjective
  exact Finset.le_inf' _ _ fun j _ ↦ pairCost_nonneg istar j

/-- **The platform's optimality implies optimality for the closed-form
objective**, on the nonnegative reals. -/
theorem isOptimalAllo_coe [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.erase istar).Nonempty)
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    {γ : Fin k → ℝ≥0} (hγpos : ∀ i, 0 < γ i)
    (hγ : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) γ) :
    IsOptimalAllo hne μvec (fun j ↦ (γ j : ℝ)) := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  rw [isOptimalAllocation_iff] at hγ
  obtain ⟨hsum, hdom⟩ := hγ
  constructor
  · refine ⟨fun j ↦ (γ j).coe_nonneg, ?_⟩
    rw [← NNReal.coe_sum, hsum, NNReal.coe_one]
  · intro b hb
    obtain ⟨j₁, hj₁mem⟩ := id hne'
    have hj₁ : j₁ ≠ istar := by simpa using hj₁mem
    set b' : Fin k → ℝ≥0 := fun j ↦ ⟨b j, hb.1 j⟩ with hb'def
    have hbcoe : (fun j ↦ ((b' j : ℝ))) = b := rfl
    have hb'sum : ∑ j, b' j = 1 := by
      apply NNReal.coe_injective
      rw [NNReal.coe_sum, NNReal.coe_one]
      exact hb.2
    by_cases hb'pos : ∀ i, 0 < b' i
    · have hcmp := hdom b' hb'sum
      rw [innerInf_eq_ofReal hstar hne' hb'pos,
        innerInf_eq_ofReal hstar hne' hγpos] at hcmp
      have hle : allocObjective μvec istar hne' b'
          ≤ allocObjective μvec istar hne' γ :=
        (ENNReal.ofReal_le_ofReal_iff (allocObjective_nonneg hne' γ)).mp hcmp
      show alloRate hne μvec b ≤ alloRate hne μvec fun j ↦ ((γ j : ℝ))
      rw [← hbcoe, alloRate_eq_allocObjective hne hne',
        alloRate_eq_allocObjective hne hne']
      exact hle
    · -- a degenerate competitor scores `0`, which no optimal allocation is below
      push_neg at hb'pos
      obtain ⟨i₀, hi₀⟩ := hb'pos
      have hzero : b i₀ = 0 := by
        have h1 : b' i₀ = 0 := le_antisymm hi₀ zero_le'
        have h2 : ((b' i₀ : ℝ≥0) : ℝ) = b i₀ := rfl
        rw [← h2, h1, NNReal.coe_zero]
      have hbzero : alloRate hne μvec b ≤ 0 := by
        by_cases hi₀star : i₀ = istar
        · have hle := alloRate_le hne μvec b hj₁
          unfold harmCost at hle
          rw [show b istar = 0 by rw [← hi₀star]; exact hzero,
            pairHarm_zero_left] at hle
          simpa using hle
        · have hle := alloRate_le hne μvec b hi₀star
          unfold harmCost at hle
          rw [hzero, pairHarm_zero_right] at hle
          simpa using hle
      exact le_trans hbzero (alloRate_nonneg hne (fun j ↦ (γ j).coe_nonneg))


/-! ## Uniqueness at the platform level -/

/-- **The optimal allocation of a Gaussian bandit with a strictly best arm is
unique.**  Garivier & Kaufmann, Lemma 4, in the vocabulary of L&S Eq. (33.4). -/
theorem isOptimalAllocation_unique [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α β : Fin k → ℝ≥0}
    (hα : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) α)
    (hβ : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) β) : α = β := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hαpos := pos_of_isOptimalAllocation hstar hα
  have hβpos := pos_of_isOptimalAllocation hstar hβ
  -- there is a competing arm, else the two allocations are both `δ_{istar}`
  rcases (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).eq_empty_or_nonempty with
    hSe | hne'
  · have hall : ∀ j : Fin k, j = istar := by
      intro j
      by_contra hj
      have : j ∈ Finset.univ.filter fun l : Fin k ↦ l ≠ istar := by simp [hj]
      rw [hSe] at this
      exact absurd this (Finset.notMem_empty j)
    have hone : ∀ γ : Fin k → ℝ≥0, ∑ j, γ j = 1 → ∀ j, γ j = 1 := by
      intro γ hγ j
      have hsingle : ∑ l : Fin k, γ l = γ istar :=
        Finset.sum_eq_single istar (fun l _ hl ↦ absurd (hall l) hl)
          (fun h ↦ absurd (Finset.mem_univ istar) h)
      rw [hall j, ← hsingle, hγ]
    funext j
    rw [hone α ((isOptimalAllocation_iff μvec α).mp hα).1 j,
      hone β ((isOptimalAllocation_iff μvec β).mp hβ).1 j]
  · -- transport to the closed form and apply uniqueness there
    have hne : (Finset.univ.erase istar).Nonempty := by
      rw [erase_eq_filter_ne]; exact hne'
    have hμ : ∀ j, j ≠ istar → μvec j ≠ μvec istar := fun j hj ↦ (hstar j hj).ne
    have hopt := fun (γ : Fin k → ℝ≥0) (hγpos : ∀ i, 0 < γ i) hγ ↦
      isOptimalAllo_coe hstar hne hne' hγpos hγ
    have hαo := hopt α hαpos hα
    have hβo := hopt β hβpos hβ
    have heq : (fun j ↦ ((α j : ℝ))) = fun j ↦ ((β j : ℝ)) :=
      eq_of_isOptimal hne hμ hαo hβo
    funext j
    exact NNReal.coe_injective (congrFun heq j)

end BanditAlgorithm

/-!
# The platform's allocation is the closed-form one

`Solutions/AllocationContinuity.lean` works with `optimalAllocation hne μ`, a
real-valued maximiser of the closed-form objective
`Ψ_i(μ, α) = min_{j≠i} pairHarm(α_i, α_j)(μ_i − μ_j)²/2`, while the mission's
statements use `IsOptimalAllocation`, phrased through the `ℝ≥0∞`-valued
information infimum of Eq. (33.4) and an `ℝ≥0`-valued allocation.

The two agree wherever the best arm is strict, and this file records the
identification in the direction the settling argument needs: *there is* an
`ℝ≥0`-valued optimal allocation, it has full support, and its coercion is the
closed-form maximiser.

The only content is uniqueness.  Existence on the platform side
(`exists_isOptimalAllocation_gaussian`) and the comparison of objectives
(`isOptimalAllo_coe`) are already available; uniqueness of the closed-form
maximiser (`eq_of_isOptimal`, Garivier–Kaufmann Lemma 4) is what forces the
coercion to be *the* `optimalAllocation` rather than merely *an* optimum.
-/

open Filter Topology Finset MeasureTheory NNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- **The platform's optimal allocation, identified with the closed-form one.** -/
theorem exists_nnreal_optimalAllocation [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hne : (Finset.univ.erase istar).Nonempty)
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    ∃ α : Fin k → ℝ≥0, (∀ i, 0 < α i) ∧
      IsOptimalAllocation (gaussianBandit μvec)
        (Set.range (gaussianBandit (k := k))) α ∧
      (fun j ↦ ((α j : ℝ))) = optimalAllocation hne μvec := by
  classical
  obtain ⟨α, hαpos, hα⟩ := exists_isOptimalAllocation_gaussian hstar
  have hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty := by
    rwa [← erase_eq_filter_ne]
  have hcoe : IsOptimalAllo hne μvec (fun j ↦ ((α j : ℝ))) :=
    isOptimalAllo_coe hstar hne hne' hαpos hα
  have hμ : ∀ j, j ≠ istar → μvec j ≠ μvec istar := fun j hj ↦ (hstar j hj).ne
  refine ⟨α, hαpos, hα, ?_⟩
  exact eq_of_isOptimal hne hμ hcoe (optimalAllocation_spec hne μvec)

/-- The coordinatewise form, which is what the settling predicate needs. -/
theorem coe_eq_optimalAllocation [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    {hne : (Finset.univ.erase istar).Nonempty}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hαpos : ∀ i, 0 < α i)
    (hα : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) α) (j : Fin k) :
    ((α j : ℝ)) = optimalAllocation hne μvec j := by
  classical
  have hne' : (Finset.univ.filter fun l : Fin k ↦ l ≠ istar).Nonempty := by
    rwa [← erase_eq_filter_ne]
  have hcoe : IsOptimalAllo hne μvec (fun l ↦ ((α l : ℝ))) :=
    isOptimalAllo_coe hstar hne hne' hαpos hα
  have hμ : ∀ l, l ≠ istar → μvec l ≠ μvec istar := fun l hl ↦ (hstar l hl).ne
  have := eq_of_isOptimal hne hμ hcoe (optimalAllocation_spec hne μvec)
  exact congrFun this j

end BanditAlgorithm

/-!
# Proposition 13 for D-Tracking

The concrete rule, checked against the two abstract nodes it was built for.

`alloc_settling_of_tracking_and_target_accuracy` asks for a tracked target that
the counts follow to within a constant and that becomes accurate once the
estimates are; `settling_of_allocation_half_and_forced_exploration` turns that,
together with the exploration floor, into the settling statement with an
integrable settling time.  So all that is left here is to check the four
hypotheses for `safePolicy`:

* **tracking** — a trajectory that follows the rule has the rule's counts
  (`Solutions/SafePolicyCounts.lean`), and the greedy tracking discrepancy is at
  most `k` (`Solutions/TrackingDiscrepancy.lean`);
* **the floor** — `T_j(t) ≥ √t − 2k` almost surely, the same statement;
* **accuracy of the target** — continuity of the plug-in map at `μ` gives an `ε`
  that converts into `ξ/4` (`Solutions/SafeAllocationModulus.lean`), and the
  exploration floor contributes another `ξ/4` from round `floorRound k (ξ/4)`
  on, so `S₀` is that round;
* **the target is a probability vector** — by construction.

No new mathematics: the content is in the two imported nodes and in the rule's
own guarantees.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The following event -/

/-- The trajectories that play the arm the rule prescribes at every round. -/
def followSet [NeZero k] (hk2 : 2 ≤ k) : Set (ℕ → Fin k × ℝ) :=
  {ω : ℕ → Fin k × ℝ | ∀ t : ℕ, (ω t).1 = safeArm hk2 (trajMeans ω) t}

theorem measure_followSet_compl [NeZero k] (hk2 : 2 ≤ k) (ν : StochasticBandit k) :
    banditTrajMeasure ν (safePolicy hk2) (followSet hk2)ᶜ = 0 := by
  have h := safePolicy_ae_follows hk2 ν
  rw [ae_iff] at h
  exact h

/-! ## The four hypotheses -/

/-- **Tracking**, transported from the rule's counts to the trajectory's. -/
theorem tracking_on_followSet [NeZero k] (hk2 : 2 ≤ k) (ω : ℕ → Fin k × ℝ)
    (hω : ω ∈ followSet hk2) (n : ℕ) (i : Fin k) :
    |(trajPullCount i n ω : ℝ)
      - ∑ s ∈ Finset.range n, safeTarget hk2 (trajMeans ω) s i| ≤ (k : ℝ) := by
  have hcounts : (trajPullCount i n ω : ℝ)
      = (safeCounts hk2 (trajMeans ω) n i : ℝ) := by
    rw [trajPullCount_eq_safeCounts hk2 hω n i]
  rw [hcounts]
  exact abs_shortfall_le (isTracking_sTrackCounts (safeTarget hk2 (trajMeans ω)))
    (safeTarget_nonneg hk2 (trajMeans ω)) (safeTarget_sum hk2 (trajMeans ω)) n i

/-- **Accuracy of the target**: continuity plus the vanishing exploration floor. -/
theorem target_accuracy [NeZero k] (hk2 : 2 ≤ k) {μvec : Fin k → ℝ} {istar : Fin k}
    (hne : (Finset.univ.erase istar).Nonempty)
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {ξ ε : ℝ} (hξ : 0 < ξ)
    (hεspec : ∀ m : Fin k → ℝ, (∀ l, |m l - μvec l| ≤ ε) →
      ∀ j, |safeAllocation hk2 m j - optimalAllocation hne μvec j| ≤ ξ / 4)
    (ω : ℕ → Fin k × ℝ) (s : ℕ) (hs : floorRound k (ξ / 4) ≤ s)
    (hmeans : ∀ l, |trajEmpiricalMean l s ω - μvec l| ≤ ε) (j : Fin k) :
    |safeTarget hk2 (trajMeans ω) s j - optimalAllocation hne μvec j| ≤ ξ / 2 := by
  have h1 : |safeTarget hk2 (trajMeans ω) s j
      - safeAllocation hk2 (trajMeans ω s) j| ≤ ξ / 4 :=
    abs_safeTarget_sub_le hk2 (trajMeans ω) (by linarith) hs j
  have h2 : |safeAllocation hk2 (trajMeans ω s) j
      - optimalAllocation hne μvec j| ≤ ξ / 4 :=
    hεspec (trajMeans ω s) (fun l ↦ hmeans l) j
  have h3 := abs_sub_le (safeTarget hk2 (trajMeans ω) s j)
    (safeAllocation hk2 (trajMeans ω s) j) (optimalAllocation hne μvec j)
  linarith

/-! ## Proposition 13 for the D-Tracking policy -/

/-- **Both halves, for `safePolicy`.** -/
theorem prop13_safePolicy_inlined [NeZero k] (hk2 : 2 ≤ k) {μvec : Fin k → ℝ}
    {istar : Fin k} (hne : (Finset.univ.erase istar).Nonempty)
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {ξ : ℝ} (hξ : 0 < ξ) :
    (∀ᵐ ω ∂(banditTrajMeasure (gaussianBandit μvec) (safePolicy hk2)),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (0 < n ∧
            (∀ i, |trajAllocation i n ω - optimalAllocation hne μvec i| ≤ ξ) ∧
            (∀ i, |trajEmpiricalMean i n ω - μvec i| ≤ ξ)))
      ∧ ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
          (0 < n ∧
            (∀ i, |trajAllocation i n ω - optimalAllocation hne μvec i| ≤ ξ) ∧
            (∀ i, |trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
        ∂(banditTrajMeasure (gaussianBandit μvec) (safePolicy hk2)) ≠ ⊤ := by
  classical
  -- the exploration floor, almost surely
  have hcount : ∀ᵐ ω ∂(banditTrajMeasure (gaussianBandit μvec) (safePolicy hk2)),
      ∀ (t : ℕ) (j : Fin k),
        Real.sqrt (t : ℝ) - 2 * (k : ℝ) ≤ (trajPullCount j t ω : ℝ) :=
    safePolicy_ae_sqrt_sub_le_trajPullCount hk2 (gaussianBandit μvec)
  -- the accuracy of the means that continuity converts into `ξ/4`
  obtain ⟨ε, hε, hεspec⟩ :=
    exists_eps_of_strict_max hk2 hne hstar (ζ := ξ / 4) (by linarith)
  -- the allocation half, from the abstract node
  have halloc := alloc_settling_of_tracking_and_target_accuracy
    (k := k) μvec (safePolicy hk2)
    (p := fun ω s ↦ safeTarget hk2 (trajMeans ω) s)
    (α := optimalAllocation hne μvec) (C := (k : ℝ)) (Nat.cast_nonneg k)
    (G := followSet hk2) (measure_followSet_compl hk2 (gaussianBandit μvec))
    (fun i ↦ (optimalAllocation_mem hne μvec).1 i)
    (fun i ↦ le_one_of_mem_alloSimplex (optimalAllocation_mem hne μvec) i)
    (fun ω s i ↦ safeTarget_nonneg hk2 (trajMeans ω) s i)
    (fun ω s i ↦ le_one_of_mem_alloSimplex
      ⟨fun l ↦ safeTarget_nonneg hk2 (trajMeans ω) s l,
       safeTarget_sum hk2 (trajMeans ω) s⟩ i)
    (fun ω hω n i ↦ tracking_on_followSet hk2 ω hω n i)
    hcount hξ hε (S₀ := floorRound k (ξ / 4))
    (fun ω _ s hs hmeans j ↦ target_accuracy hk2 hne hstar hξ hεspec ω s hs hmeans j)
  -- and the settling assembly
  exact settling_of_allocation_half_and_forced_exploration μvec (safePolicy hk2)
    (optimalAllocation hne μvec) hξ hcount halloc.1 halloc.2

/-! ## The package -/

/-- **One policy, Proposition 13 for every environment with `k ≥ 2` arms.** -/
theorem exists_policy_prop13_two_le [NeZero k] (hk2 : 2 ≤ k) :
    ∃ pol : BanditPolicy k,
      ∀ (μvec : Fin k → ℝ) (istar : Fin k),
        (∀ j, j ≠ istar → μvec j < μvec istar) →
        ∃ α : Fin k → ℝ≥0, (∀ i, 0 < α i) ∧
          IsOptimalAllocation (gaussianBandit μvec)
            (Set.range (gaussianBandit (k := k))) α ∧
          ∀ ξ : ℝ, 0 < ξ →
            (∀ᵐ ω ∂(banditTrajMeasure (gaussianBandit μvec) pol),
                ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                  (0 < n ∧
                    (∀ i, |trajAllocation i n ω - ((α i : ℝ))| ≤ ξ) ∧
                    (∀ i, |trajEmpiricalMean i n ω - μvec i| ≤ ξ)))
              ∧ ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
                  (0 < n ∧
                    (∀ i, |trajAllocation i n ω - ((α i : ℝ))| ≤ ξ) ∧
                    (∀ i, |trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
                ∂(banditTrajMeasure (gaussianBandit μvec) pol) ≠ ⊤ := by
  classical
  refine ⟨safePolicy hk2, fun μvec istar hstar ↦ ?_⟩
  have hne : (Finset.univ.erase istar).Nonempty := erase_nonempty_of_two_le hk2 istar
  obtain ⟨α, hαpos, hα, hcoe⟩ := exists_nnreal_optimalAllocation hne hstar
  refine ⟨α, hαpos, hα, fun ξ hξ ↦ ?_⟩
  have hfun : (fun i ↦ ((α i : ℝ))) = optimalAllocation hne μvec := hcoe
  have hpt : ∀ i, ((α i : ℝ)) = optimalAllocation hne μvec i := fun i ↦ congrFun hfun i
  simp only [hpt]
  exact prop13_safePolicy_inlined hk2 hne hstar hξ

end BanditAlgorithm

open BanditAlgorithm

theorem solution {k : ℕ} [NeZero k] (hk2 : 2 ≤ k) :
    ∃ pol : BanditAlgorithm.BanditPolicy k,
      ∀ (μvec : Fin k → ℝ) (istar : Fin k),
        (∀ j, j ≠ istar → μvec j < μvec istar) →
        ∃ α : Fin k → NNReal,
          (∀ i, 0 < α i) ∧
          BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
              (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α ∧
          ∀ ξ : ℝ, 0 < ξ →
          (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol),
              ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))) ∧
            ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
                (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
              ∂(BanditAlgorithm.banditTrajMeasure
                (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤ :=
  BanditAlgorithm.exists_policy_prop13_two_le hk2
