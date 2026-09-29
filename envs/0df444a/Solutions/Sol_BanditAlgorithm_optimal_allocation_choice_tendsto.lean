-- Prove2me | solution 1 for BanditAlgorithm.optimal_allocation_choice_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T05:25:05.721885+00:00
-- url     : https://prove2.me/submissions/d543c7c0-5e06-46b3-b067-640b4f0d6fdb

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Theorems.Thm_BanditAlgorithm_gaussian_optimal_allocation_unique
import Theorems.Thm_BanditAlgorithm_argmax_dist_le_of_unique_maximiser
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
  obtain ⟨δ, hδ, h⟩ := argmax_dist_le_of_unique_maximiser hS hF (a₀ := a₀)
    (fun a haS hamax ↦ huniq a ⟨haS, hamax⟩) hε
  exact ⟨δ, hδ, fun x hx a ha ↦ h x hx a ha.1 ha.2⟩

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
      (Set.range (gaussianBandit (k := k))) β) : α = β :=
  gaussian_optimal_allocation_unique hstar hα hβ

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
# Any rule that picks optimal allocations is continuous where the best arm is strict

The D-Tracking guarantee is stated with an arbitrary *rule*

  `choice : (Fin k → ℝ) → Fin k → ℝ≥0`

assigning to each Gaussian parameter vector with a unique best arm a full-support
optimal allocation, and asks for a sampling rule whose empirical allocation
converges to `choice μ`.  The rule is arbitrary, so nothing about it is assumed —
in particular not continuity, which is exactly what a tracking argument needs.

That is not an oversight, because there is nothing to choose:
`isOptimalAllocation_unique` says an optimal allocation is *the* optimal
allocation.  So `choice` is pinned down on every parameter with a strictly best
arm, agrees there with the canonical selection of
`Solutions/AllocationContinuity.lean`, and inherits its continuity.

This file makes that precise:

* `choice_eq_of_isOptimal` — two rules satisfying the hypothesis agree wherever
  the best arm is strict;
* `tendsto_choice` — along estimates converging to such a parameter,
  `choice(μ̂(s)) → choice(μ)`.

The second is the form the tracking argument consumes, and it is stated for
estimates rather than as a continuity statement because the estimates that are
fed to `choice` need not have a strictly best arm at every round — only
eventually, which `eventually_strictly_best_seq` supplies.  A rule is free to
return nonsense at parameters with ties, and the argument never looks at those
rounds.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter Topology Finset

namespace BanditAlgorithm

variable {k : ℕ}

/-- The hypothesis carried by the D-Tracking statement: `choice` returns a
full-support optimal allocation at every parameter with a unique best arm. -/
def IsOptimalChoice [NeZero k] (choice : (Fin k → ℝ) → Fin k → ℝ≥0) : Prop :=
  ∀ μvec : Fin k → ℝ, (∃ istar : Fin k, ∀ j, j ≠ istar → μvec j < μvec istar) →
    (∀ i, 0 < choice μvec i) ∧
      IsOptimalAllocation (gaussianBandit μvec)
        (Set.range (gaussianBandit (k := k))) (choice μvec)

/-! ## The rule is forced -/

/-- **Any two admissible rules agree where the best arm is strict.** -/
theorem choice_eq_of_isOptimal [NeZero k] {choice choice' : (Fin k → ℝ) → Fin k → ℝ≥0}
    (h : IsOptimalChoice choice) (h' : IsOptimalChoice choice')
    {μvec : Fin k → ℝ} {istar : Fin k} (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    choice μvec = choice' μvec :=
  isOptimalAllocation_unique hstar (h μvec ⟨istar, hstar⟩).2 (h' μvec ⟨istar, hstar⟩).2

/-- The real-valued form of the rule, which is what the allocation objective
takes as its argument. -/
noncomputable def choiceReal [NeZero k] (choice : (Fin k → ℝ) → Fin k → ℝ≥0)
    (μvec : Fin k → ℝ) : Fin k → ℝ :=
  fun j ↦ ((choice μvec j : ℝ))

/-- At a parameter with a strictly best arm, the rule's value is a maximiser of
the closed-form objective. -/
theorem isOptimalAllo_choiceReal [NeZero k] {choice : (Fin k → ℝ) → Fin k → ℝ≥0}
    (h : IsOptimalChoice choice) {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.erase istar).Nonempty)
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty) :
    IsOptimalAllo hne μvec (choiceReal choice μvec) :=
  isOptimalAllo_coe hstar hne hne' (h μvec ⟨istar, hstar⟩).1 (h μvec ⟨istar, hstar⟩).2

/-- Hence it agrees with the canonical selection. -/
theorem choiceReal_eq_optimalAllocation [NeZero k]
    {choice : (Fin k → ℝ) → Fin k → ℝ≥0} (h : IsOptimalChoice choice)
    {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.erase istar).Nonempty)
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty) :
    choiceReal choice μvec = optimalAllocation hne μvec :=
  eq_optimalAllocation hne (fun j hj ↦ (hstar j hj).ne)
    (isOptimalAllo_choiceReal h hstar hne hne')

/-! ## Convergence along estimates -/

/-- **The plug-in allocations converge.**  Along any sequence of estimates
converging to a parameter with a strictly best arm, the rule's outputs converge
to its output at the limit — even though the rule was never assumed continuous,
and even though early estimates may have ties. -/
theorem tendsto_choiceReal [NeZero k] {choice : (Fin k → ℝ) → Fin k → ℝ≥0}
    (h : IsOptimalChoice choice) {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.erase istar).Nonempty)
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    {m : ℕ → Fin k → ℝ} (hm : Tendsto m atTop (𝓝 μvec)) :
    Tendsto (fun s ↦ choiceReal choice (m s)) atTop
      (𝓝 (choiceReal choice μvec)) := by
  have hμ : ∀ j, j ≠ istar → μvec j ≠ μvec istar := fun j hj ↦ (hstar j hj).ne
  -- from some round on, the estimates also have `istar` strictly best
  have hev : ∀ᶠ s in atTop, IsOptimalAllo hne (m s) (choiceReal choice (m s)) := by
    filter_upwards [eventually_strictly_best_seq hstar hm] with s hs
    exact isOptimalAllo_choiceReal h hs hne hne'
  have hlim : Tendsto (fun s ↦ choiceReal choice (m s)) atTop
      (𝓝 (optimalAllocation hne μvec)) := by
    refine tendsto_of_eventually_isMaxOnSet isCompact_alloSimplex
      (continuousOn_alloRate hne) (a₀ := optimalAllocation hne μvec) ?_ hm hev
    intro a ha
    exact eq_of_isOptimal hne hμ ha (optimalAllocation_spec hne μvec)
  rwa [← choiceReal_eq_optimalAllocation h hstar hne hne'] at hlim

/-- Coordinatewise. -/
theorem tendsto_choiceReal_coord [NeZero k] {choice : (Fin k → ℝ) → Fin k → ℝ≥0}
    (h : IsOptimalChoice choice) {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.erase istar).Nonempty)
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    {m : ℕ → Fin k → ℝ} (hm : Tendsto m atTop (𝓝 μvec)) (j : Fin k) :
    Tendsto (fun s ↦ ((choice (m s) j : ℝ))) atTop (𝓝 ((choice μvec j : ℝ))) :=
  ((continuous_apply j).continuousAt.tendsto).comp
    (tendsto_choiceReal h hstar hne hne' hm)

/-! ## The rule's values lie in the simplex

Recorded separately because the tracking construction needs it as a hypothesis
about the target sequence, not as a statement about a limit. -/

theorem choiceReal_mem_alloSimplex [NeZero k] {choice : (Fin k → ℝ) → Fin k → ℝ≥0}
    (h : IsOptimalChoice choice) {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    choiceReal choice μvec ∈ alloSimplex k := by
  refine ⟨fun j ↦ (choice μvec j).coe_nonneg, ?_⟩
  have hsum := ((isOptimalAllocation_iff μvec (choice μvec)).mp
    (h μvec ⟨istar, hstar⟩).2).1
  unfold choiceReal
  rw [← NNReal.coe_sum, hsum, NNReal.coe_one]

end BanditAlgorithm

theorem _root_.solution {k : ℕ} [NeZero k]
    (choice : (Fin k → ℝ) → Fin k → NNReal)
    (hchoice : ∀ m : Fin k → ℝ, (∃ i : Fin k, ∀ j, j ≠ i → m j < m i) →
      (∀ i, 0 < choice m i) ∧
        BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit m)
          (Set.range (BanditAlgorithm.gaussianBandit (k := k))) (choice m))
    {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hne : (Finset.univ.erase istar).Nonempty)
    (hne' : (Finset.univ.filter fun j : Fin k ↦ j ≠ istar).Nonempty)
    {m : ℕ → Fin k → ℝ} (hm : Filter.Tendsto m Filter.atTop (nhds μvec))
    (j : Fin k) :
    Filter.Tendsto (fun s ↦ ((choice (m s) j : ℝ))) Filter.atTop
      (nhds ((choice μvec j : ℝ))) :=
  BanditAlgorithm.tendsto_choiceReal_coord (choice := choice) hchoice hstar hne hne' hm j
