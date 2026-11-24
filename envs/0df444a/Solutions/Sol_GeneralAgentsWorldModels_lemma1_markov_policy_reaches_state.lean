-- Prove2me | solution 1 for GeneralAgentsWorldModels.lemma1_markov_policy_reaches_state
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:44:55.876472+00:00
-- url     : https://prove2.me/submissions/cfe19d6e-e837-4e1c-936a-f9895bc361ab

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

set_option autoImplicit false

universe u v

namespace GeneralAgentsWorldModels

section L1

variable {S A : Type*} [Fintype S]

/-- Splitting a sum over `Fin (n+1) → S` into the first next state and the rest. -/
theorem l1_sum_ofFn_succ {β : Type*} [AddCommMonoid β] (f : List S → β) (n : ℕ) :
    ∑ ss : Fin (n + 1) → S, f (List.ofFn ss) =
      ∑ y : S, ∑ ss : Fin n → S, f (y :: List.ofFn ss) := by
  rw [← (Fin.consEquiv (fun _ => S)).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv, List.ofFn_succ]

theorem l1_pathWeight_nonneg (M : CMP S A) (π : Policy S A) :
    ∀ (l : List S) (h : List (S × A)) (s : S), 0 ≤ pathWeight M π h s l
  | [], h, s => by simp [pathWeight]
  | y :: l, h, s => by
    simp only [pathWeight]
    exact mul_nonneg (M.nonneg _ _ _) (l1_pathWeight_nonneg M π l _ _)

theorem l1_sum_pathWeight (M : CMP S A) (π : Policy S A) :
    ∀ (n : ℕ) (h : List (S × A)) (s : S),
      ∑ ss : Fin n → S, pathWeight M π h s (List.ofFn ss) = 1
  | 0, h, s => by simp [pathWeight]
  | n + 1, h, s => by
    rw [l1_sum_ofFn_succ]
    simp only [pathWeight]
    simp_rw [← Finset.mul_sum, l1_sum_pathWeight M π n, mul_one]
    exact M.sum_one _ _

theorem l1_succProbUpTo_nonneg (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S)
    (T : ℕ) : 0 ≤ succProbUpTo M ψ π s T := by
  unfold succProbUpTo
  refine Finset.sum_nonneg fun ss _ => mul_nonneg (l1_pathWeight_nonneg _ _ _ _ _) ?_
  split_ifs <;> norm_num

theorem l1_succProbUpTo_le_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S)
    (T : ℕ) : succProbUpTo M ψ π s T ≤ 1 := by
  unfold succProbUpTo
  calc _ ≤ ∑ ss : Fin T → S, pathWeight M π [] s (List.ofFn ss) := by
        refine Finset.sum_le_sum fun ss _ => ?_
        have := l1_pathWeight_nonneg M π (List.ofFn ss) [] s
        split_ifs <;> simp [this]
    _ = 1 := l1_sum_pathWeight M π T [] s

theorem l1_succProbUpTo_bddAbove (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S) :
    BddAbove (Set.range fun T => succProbUpTo M ψ π s T) :=
  ⟨1, by rintro _ ⟨T, rfl⟩; exact l1_succProbUpTo_le_one M ψ π s T⟩

theorem l1_succProb_le_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S) :
    succProb M ψ π s ≤ 1 :=
  ciSup_le fun T => l1_succProbUpTo_le_one M ψ π s T

theorem l1_succProbUpTo_le_succProb (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S)
    (T : ℕ) : succProbUpTo M ψ π s T ≤ succProb M ψ π s :=
  le_ciSup (l1_succProbUpTo_bddAbove M ψ π s) T

omit [Fintype S] in
theorem l1_prefix_pathPrefix (π : Policy S A) :
    ∀ (l : List S) (h : List (S × A)) (s : S), h ++ [(s, π h s)] <+: pathPrefix π h s l
  | [], h, s => by simp [pathPrefix]
  | y :: l, h, s => by
    simp only [pathPrefix]
    exact (List.prefix_append _ _).trans (l1_prefix_pathPrefix π l _ _)

omit [Fintype S] in
theorem l1_mem_pathPrefix_markov (μ : S → A) :
    ∀ (l : List S) (h : List (S × A)) (s z : S), z ∈ s :: l →
      (z, μ z) ∈ pathPrefix (fun _ x => μ x) h s l
  | [], h, s, z, hz => by
    simp at hz; subst hz; simp [pathPrefix]
  | y :: l, h, s, z, hz => by
    simp only [pathPrefix]
    rcases List.mem_cons.1 hz with rfl | hz
    · exact (l1_prefix_pathPrefix (fun _ x => μ x) l _ y).subset (by simp)
    · exact l1_mem_pathPrefix_markov μ l _ y z hz

omit [Fintype S] in
/-- A prefix containing a pair of `g` decides the goal `◇ g`. -/
theorem l1_decides_eventually (g : Set (S × A)) (pre : List (S × A)) (p : S × A)
    (hp : p ∈ pre) (hg : p ∈ g) :
    Decides [[(⟨opEventually, g⟩ : SubGoal S A)]] pre := by
  classical
  intro τ hτ
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  have hex : ∃ u, τ u ∈ g := ⟨i, by rw [hτ i hi]; exact hg⟩
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [seqSat]
  rw [if_neg (by decide), if_neg (by decide)]
  exact ⟨Nat.find hex, Nat.zero_le _, fun v _ hv => Nat.find_min hex hv, Nat.find_spec hex,
    trivial⟩

variable [DecidableEq S]

/-- Probability, under the Markov policy `μ`, of visiting `s'` among the states at times
`0, …, n`, starting from `x`. -/
def l1_hit (M : CMP S A) (μ : S → A) (s' : S) : ℕ → S → ℝ
  | 0, x => if x = s' then 1 else 0
  | n + 1, x => if x = s' then 1 else ∑ y, M.P x (μ x) y * l1_hit M μ s' n y

theorem l1_sum_hit (M : CMP S A) (μ : S → A) (s' : S) :
    ∀ (n : ℕ) (h : List (S × A)) (x : S),
      ∑ ss : Fin n → S, pathWeight M (fun _ z => μ z) h x (List.ofFn ss) *
        (if s' ∈ x :: List.ofFn ss then 1 else 0) = l1_hit M μ s' n x
  | 0, h, x => by
    simp [pathWeight, l1_hit, eq_comm]
  | n + 1, h, x => by
    rw [l1_sum_ofFn_succ (fun l => pathWeight M (fun _ z => μ z) h x l *
      if s' ∈ x :: l then (1 : ℝ) else 0)]
    simp only [pathWeight, l1_hit]
    by_cases hx : x = s'
    · subst hx
      simp only [List.mem_cons, true_or, if_true, mul_one]
      simp_rw [← Finset.mul_sum, l1_sum_pathWeight, mul_one]
      exact M.sum_one _ _
    · rw [if_neg hx]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← l1_sum_hit M μ s' n (h ++ [(x, μ x)]) y, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ss _ => ?_
      have : (s' ∈ x :: y :: List.ofFn ss) ↔ (s' ∈ y :: List.ofFn ss) := by
        rw [List.mem_cons (l := y :: _)]
        exact ⟨fun h => h.resolve_left (Ne.symm hx), Or.inr⟩
      simp only [this, mul_assoc]

theorem l1_hit_bounds (M : CMP S A) (μ : S → A) (s' : S) :
    ∀ (n : ℕ) (x : S), 0 ≤ l1_hit M μ s' n x ∧ l1_hit M μ s' n x ≤ 1
  | 0, x => by simp only [l1_hit]; split_ifs <;> norm_num
  | n + 1, x => by
    simp only [l1_hit]
    split_ifs
    · norm_num
    constructor
    · exact sum_nonneg fun y _ =>
        mul_nonneg (M.nonneg _ _ _) (l1_hit_bounds M μ s' n y).1
    · calc _ ≤ ∑ y, M.P x (μ x) y * 1 := sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (l1_hit_bounds M μ s' n y).2 (M.nonneg _ _ _)
        _ = 1 := by simp [M.sum_one]

theorem l1_hit_self (M : CMP S A) (μ : S → A) (s' : S) (n : ℕ) : l1_hit M μ s' n s' = 1 := by
  cases n <;> simp [l1_hit]

theorem l1_hit_shift (M : CMP S A) (μ : S → A) (s' : S) (a : ℕ) (c : ℝ)
    (hc : ∀ y, 1 - l1_hit M μ s' a y ≤ c) :
    ∀ (n : ℕ) (x : S), 1 - l1_hit M μ s' (n + a) x ≤ c * (1 - l1_hit M μ s' n x)
  | 0, x => by
    rw [Nat.zero_add]
    by_cases hx : x = s'
    · subst hx; simp [l1_hit_self]
    · simpa [l1_hit, hx] using hc x
  | n + 1, x => by
    rw [show n + 1 + a = (n + a) + 1 by omega]
    by_cases hx : x = s'
    · subst hx; simp [l1_hit_self]
    simp only [l1_hit, if_neg hx]
    have key : ∀ f : S → ℝ, 1 - ∑ y, M.P x (μ x) y * f y = ∑ y, M.P x (μ x) y * (1 - f y) := by
      intro f; simp [mul_sub, sum_sub_distrib, M.sum_one]
    rw [key, key, Finset.mul_sum]
    refine sum_le_sum fun y _ => ?_
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (l1_hit_shift M μ s' a c hc n y) (M.nonneg _ _ _)

/-- States from which `s'` is reachable in at most `k` positive-probability transitions. -/
def l1_W (M : CMP S A) (s' : S) : ℕ → Set S
  | 0 => {s'}
  | k + 1 => l1_W M s' k ∪ {x | ∃ a y, 0 < M.P x a y ∧ y ∈ l1_W M s' k}

omit [DecidableEq S] in
theorem l1_W_of_transGen (M : CMP S A) (s' : S) (x : S)
    (ht : Relation.TransGen (fun x y => ∃ a, 0 < M.P x a y) x s') :
    ∃ k, x ∈ l1_W M s' k := by
  induction ht using Relation.TransGen.head_induction_on with
  | single h =>
    obtain ⟨a, ha⟩ := h
    exact ⟨1, Or.inr ⟨a, s', ha, rfl⟩⟩
  | @head a c h _ ih =>
    obtain ⟨b, hb⟩ := h
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, Or.inr ⟨b, c, hb, hk⟩⟩

theorem l1_W_exists (M : CMP S A) (hM : M.IsCommunicating) (s' : S) (x : S) :
    ∃ k, x ∈ l1_W M s' k := by
  by_cases hx : x = s'
  · exact ⟨0, by simp [l1_W, hx]⟩
  exact l1_W_of_transGen M s' x (hM x s' hx)

/-- Under a communicating cMP, there is a Markov policy, with prescribed action `a0` at `s'`,
whose probability of visiting `s'` within `T` steps tends to `1` uniformly in the start. -/
theorem l1_exists_markov_hit (M : CMP S A) (hM : M.IsCommunicating) (s' : S) (a0 : A) :
    ∃ μ : S → A, μ s' = a0 ∧ ∀ ε > 0, ∃ T, ∀ x, 1 - l1_hit M μ s' T x < ε := by
  classical
  have hex := l1_W_exists M hM s'
  let kf : S → ℕ := fun x => Nat.find (hex x)
  have key : ∀ x, x ≠ s' → ∃ a y, 0 < M.P x a y ∧ kf y < kf x := by
    intro x hx
    have hk : x ∈ l1_W M s' (kf x) := Nat.find_spec (hex x)
    obtain ⟨j, hj⟩ : ∃ j, kf x = j + 1 := by
      rcases h0 : kf x with _ | j
      · rw [h0] at hk; simp [l1_W] at hk; exact absurd hk hx
      · exact ⟨j, rfl⟩
    have hnj : x ∉ l1_W M s' j := Nat.find_min (hex x) (show j < kf x by omega)
    rw [hj] at hk
    rcases hk with hk | ⟨a, y, hpos, hy⟩
    · exact absurd hk hnj
    · exact ⟨a, y, hpos, lt_of_le_of_lt (Nat.find_min' (hex y) hy) (by omega)⟩
  have : Nonempty A := ⟨a0⟩
  choose! fa fy hpos hlt using key
  let μ : S → A := fun x => if x = s' then a0 else fa x
  let q : S → ℝ := fun x => if x = s' then 1 else M.P x (fa x) (fy x)
  let p : ℝ := univ.inf' ⟨s', mem_univ _⟩ q
  have hp0 : 0 < p := by
    refine (Finset.lt_inf'_iff _).2 fun x _ => ?_
    by_cases hx : x = s'
    · simp [q, hx]
    · simpa [q, hx] using hpos x hx
  have hpq : ∀ x, p ≤ q x := fun x => Finset.inf'_le _ (mem_univ x)
  have hp1 : p ≤ 1 := by simpa [q] using hpq s'
  have claim : ∀ j x, kf x ≤ j → p ^ j ≤ l1_hit M μ s' j x := by
    intro j
    induction j with
    | zero =>
      intro x hx
      have hk : x ∈ l1_W M s' (kf x) := Nat.find_spec (hex x)
      rw [show kf x = 0 by omega] at hk
      simp only [l1_W, Set.mem_singleton_iff] at hk
      subst hk; simp [l1_hit]
    | succ j ih =>
      intro x hx
      by_cases hxs : x = s'
      · subst hxs; rw [l1_hit_self]; exact pow_le_one₀ hp0.le hp1
      simp only [l1_hit, if_neg hxs]
      have hμ : μ x = fa x := by simp [μ, hxs]
      rw [hμ]
      calc p ^ (j + 1) = p * p ^ j := pow_succ' p j
        _ ≤ M.P x (fa x) (fy x) * l1_hit M μ s' j (fy x) := by
          refine mul_le_mul ?_ (ih _ (by have := hlt x hxs; omega)) (pow_nonneg hp0.le _)
            (M.nonneg _ _ _)
          simpa [q, hxs] using hpq x
        _ ≤ ∑ y, M.P x (fa x) y * l1_hit M μ s' j y :=
          Finset.single_le_sum (f := fun y => M.P x (fa x) y * l1_hit M μ s' j y)
            (fun y _ => mul_nonneg (M.nonneg _ _ _) (l1_hit_bounds M μ s' j y).1) (mem_univ _)
  let K : ℕ := univ.sup kf
  let c : ℝ := 1 - p ^ K
  have hcK : ∀ y, 1 - l1_hit M μ s' K y ≤ c := by
    intro y
    have := claim K y (Finset.le_sup (f := kf) (mem_univ y))
    simp only [c]; linarith
  have hc0 : 0 ≤ c := by simp only [c]; linarith [pow_le_one₀ (n := K) hp0.le hp1]
  have hc1 : c < 1 := by simp only [c]; linarith [pow_pos hp0 K]
  have hpow : ∀ m x, 1 - l1_hit M μ s' (m * K) x ≤ c ^ m := by
    intro m
    induction m with
    | zero => intro x; simp only [zero_mul, pow_zero]; linarith [(l1_hit_bounds M μ s' 0 x).1]
    | succ m ih =>
      intro x
      rw [Nat.succ_mul, pow_succ']
      exact (l1_hit_shift M μ s' K c hcK (m * K) x).trans
        (mul_le_mul_of_nonneg_left (ih x) hc0)
  refine ⟨μ, by simp [μ], fun ε hε => ?_⟩
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hc1
  exact ⟨m * K, fun x => (hpow m x).trans_lt hm⟩

/-- If the Markov policy `μ` visits `s'` with probability tending to `1`, then it achieves
`◇ g` with probability one for any `g` containing `(s', μ s')`. -/
theorem l1_succProb_markov_eq_one (M : CMP S A) (μ : S → A) (s' : S) (g : Set (S × A))
    (hg : (s', μ s') ∈ g) (x : S) (hconv : ∀ ε > 0, ∃ T, 1 - l1_hit M μ s' T x < ε) :
    succProb M [[(⟨opEventually, g⟩ : SubGoal S A)]] (fun _ z => μ z) x = 1 := by
  classical
  have lower : ∀ T, l1_hit M μ s' T x ≤
      succProbUpTo M [[(⟨opEventually, g⟩ : SubGoal S A)]] (fun _ z => μ z) x T := by
    intro T
    rw [← l1_sum_hit M μ s' T [] x]
    unfold succProbUpTo
    refine Finset.sum_le_sum fun ss _ =>
      mul_le_mul_of_nonneg_left ?_ (l1_pathWeight_nonneg _ _ _ _ _)
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (l1_decides_eventually g _ _ (l1_mem_pathPrefix_markov μ _ [] x s' h1) hg) h2
    · norm_num
    · exact le_rfl
  refine le_antisymm (l1_succProb_le_one _ _ _ _) (le_of_forall_pos_lt_add fun ε hε => ?_)
  obtain ⟨T, hT⟩ := hconv ε hε
  have := (lower T).trans (l1_succProbUpTo_le_succProb M _ _ x T)
  linarith

/-- Lemma 1, with the action at `s'` prescribed: a Markov policy `μ` with `μ s' = a0` reaches
`s'` (and hence visits `(s', a0)`) with probability one from every initial state. -/
theorem l1_markov_reach (M : CMP S A) (hM : M.IsCommunicating) (s' : S) (a0 : A) :
    ∃ μ : S → A, μ s' = a0 ∧ ∀ x : S,
      succProb M [[evState s']] (fun _ z => μ z) x = 1 ∧
      succProb M [[evVisit s' a0]] (fun _ z => μ z) x = 1 := by
  obtain ⟨μ, hμ, hconv⟩ := l1_exists_markov_hit M hM s' a0
  refine ⟨μ, hμ, fun x => ⟨?_, ?_⟩⟩
  · exact l1_succProb_markov_eq_one M μ s' {z | z.1 = s'} rfl x
      (fun ε hε => (hconv ε hε).imp fun T h => h x)
  · exact l1_succProb_markov_eq_one M μ s' {(s', a0)} (by simp [hμ]) x
      (fun ε hε => (hconv ε hε).imp fun T h => h x)

end L1

end GeneralAgentsWorldModels

open GeneralAgentsWorldModels in
theorem solution {S : Type u} {A : Type v} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (s' : S) :
    ∃ μ : S → A, ∀ s : S, s ≠ s' →
      succProb M [[evState s']] (fun _ x => μ x) s = 1 := by
  have : Nonempty A := Fintype.card_pos_iff.1 (by have := hM.2; omega)
  obtain ⟨μ, -, h⟩ := l1_markov_reach M hM.1 s' (Classical.arbitrary A)
  exact ⟨μ, fun s _ => (h s).1⟩
