-- Prove2me | solution 1 for BanditAlgorithm.forced_exploration_sqrt_min_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T23:19:00.895347+00:00
-- url     : https://prove2.me/submissions/dd1cbfc1-bfd5-4ccd-8ab9-b9d0df78f16c

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Forced exploration: how fast a "play the least-played arm" rule fills in

Garivier & Kaufmann's D-Tracking sampling rule interleaves two behaviours: at
round `t` it plays the *least*-played arm whenever `min_i N_i(t)` has fallen below
a threshold `g(t)` (they take `g(t) ≈ √t`), and otherwise it plays whatever the
tracking step asks for.  Their Lemma 7 says that this alone forces

  `min_i N_i(t) ≥ √(t + k²) − 2k`,

so every arm is played infinitely often, at a guaranteed rate.  That is what
makes the empirical means converge, and hence what makes the whole analysis go
through; without it a sampling rule may starve an arm for an arbitrarily long
time (see `Solutions/StoppingLowerBound.lean`).

This file proves the abstract combinatorial statement behind it, with no
reference to bandits: a sequence of count vectors that increments one coordinate
per step and is *forced* to increment a minimal coordinate whenever the minimum
is below `g` satisfies

  `∀ s t, s + k · m(t) + k ≤ t → g(s) ≤ m(t)`,      `m(t) = min_i N_i(t)`.   (★)

For `g(s) = ⌊√s⌋` this reads `√(t − k m(t) − k) ≤ m(t)`, i.e.
`t ≤ m(t)² + k m(t) + k`, which is Lemma 7 up to the exact constants.

## The potential

The proof is a potential argument.  Let `c(t)` be the number of coordinates
attaining the minimum and

  `Φ(t) = k · m(t) + k − c(t)`.

`Φ` never decreases, and it *strictly* increases on every forced step: if two or
more coordinates are minimal, incrementing one of them leaves `m` alone and drops
`c` by one; if only one is minimal, incrementing it raises `m` by one, which adds
`k` to the first term and subtracts at most `k − 1` from the second.  Since
`Φ(0) = 0` and `Φ(t) ≤ k m(t) + k − 1`, at most `k m(t) + k − 1` of the first `t`
steps can have been forced — so any window of `k m(t) + k` consecutive steps
contains an unforced one, at which `g` was already below the minimum.
-/

open Finset

namespace BanditAlgorithm

variable {k : ℕ} [NeZero k]

/-! ## The minimum of a count vector -/

/-- The least-played count. -/
noncomputable def minCount (c : Fin k → ℕ) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty c

theorem minCount_le (c : Fin k → ℕ) (i : Fin k) : minCount c ≤ c i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem le_minCount {c : Fin k → ℕ} {m : ℕ} (h : ∀ i, m ≤ c i) : m ≤ minCount c :=
  Finset.le_inf' _ _ fun i _ ↦ h i

theorem exists_eq_minCount (c : Fin k → ℕ) : ∃ i, c i = minCount c := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin k)) c
  exact ⟨i, hi.symm⟩

theorem minCount_mono {c c' : Fin k → ℕ} (h : ∀ i, c i ≤ c' i) :
    minCount c ≤ minCount c' :=
  le_minCount fun i ↦ le_trans (minCount_le c i) (h i)

/-- The set of least-played arms. -/
noncomputable def argMinSet (c : Fin k → ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun i ↦ c i = minCount c

theorem argMinSet_nonempty (c : Fin k → ℕ) : (argMinSet c).Nonempty := by
  obtain ⟨i, hi⟩ := exists_eq_minCount c
  exact ⟨i, by simp [argMinSet, hi]⟩

theorem one_le_card_argMinSet (c : Fin k → ℕ) : 1 ≤ (argMinSet c).card :=
  Finset.card_pos.mpr (argMinSet_nonempty c)

theorem card_argMinSet_le (c : Fin k → ℕ) : (argMinSet c).card ≤ k := by
  have := Finset.card_filter_le (Finset.univ : Finset (Fin k))
    (fun i ↦ c i = minCount c)
  simpa [argMinSet] using this

/-! ## The rule -/

/-- A sequence of count vectors that starts at zero, increments exactly one
coordinate per round, and is forced to increment a least-played coordinate
whenever the minimum has fallen below `g`. -/
structure IsForcedExploration (N : ℕ → Fin k → ℕ) (arm : ℕ → Fin k)
    (g : ℕ → ℕ) : Prop where
  init : ∀ i, N 0 i = 0
  step : ∀ t i, N (t + 1) i = N t i + (if i = arm t then 1 else 0)
  forced : ∀ t, minCount (N t) < g t → N t (arm t) = minCount (N t)

variable {N : ℕ → Fin k → ℕ} {arm : ℕ → Fin k} {g : ℕ → ℕ}

theorem le_succ (h : IsForcedExploration N arm g) (t : ℕ) (i : Fin k) :
    N t i ≤ N (t + 1) i := by
  rw [h.step t i]; omega

theorem minCount_le_succ (h : IsForcedExploration N arm g) (t : ℕ) :
    minCount (N t) ≤ minCount (N (t + 1)) :=
  minCount_mono (le_succ h t)

theorem minCount_mono' (h : IsForcedExploration N arm g) {s t : ℕ} (hst : s ≤ t) :
    minCount (N s) ≤ minCount (N t) := by
  induction t with
  | zero =>
      have : s = 0 := by omega
      subst this; exact le_rfl
  | succ t ih =>
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (minCount_le_succ h t)
      · have : s = t + 1 := by omega
        subst this; exact le_rfl

/-! ## The potential -/

/-- `Φ(t) = k · m(t) + k − c(t)`. -/
noncomputable def potential (N : ℕ → Fin k → ℕ) (t : ℕ) : ℕ :=
  k * minCount (N t) + k - (argMinSet (N t)).card

theorem potential_zero (h : IsForcedExploration N arm g) : potential N 0 = 0 := by
  have hmin : minCount (N 0) = 0 := by
    refine le_antisymm ?_ (Nat.zero_le _)
    obtain ⟨i, hi⟩ := exists_eq_minCount (N 0)
    rw [← hi, h.init i]
  have hcard : (argMinSet (N 0)).card = k := by
    have huniv : argMinSet (N 0) = Finset.univ := by
      ext i
      simp only [argMinSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rw [h.init i, hmin]
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  rw [potential, hmin, hcard]
  omega

theorem potential_le (t : ℕ) : potential N t ≤ k * minCount (N t) + k - 1 := by
  have h1 := one_le_card_argMinSet (N t)
  rw [potential]
  omega

/-! ## The potential increases, strictly on forced steps -/

/-- If the incremented arm is not minimal, the minimum and the argmin set are
unchanged. -/
theorem step_of_not_min (h : IsForcedExploration N arm g) {t : ℕ}
    (hne : N t (arm t) ≠ minCount (N t)) :
    minCount (N (t + 1)) = minCount (N t) ∧
      argMinSet (N (t + 1)) = argMinSet (N t) := by
  have hgt : minCount (N t) < N t (arm t) :=
    lt_of_le_of_ne (minCount_le _ _) (Ne.symm hne)
  have hval : ∀ i, i ≠ arm t → N (t + 1) i = N t i := by
    intro i hi; rw [h.step t i, if_neg hi, Nat.add_zero]
  have hmin : minCount (N (t + 1)) = minCount (N t) := by
    refine le_antisymm ?_ (minCount_le_succ h t)
    obtain ⟨i, hi⟩ := exists_eq_minCount (N t)
    have hine : i ≠ arm t := by
      intro hcon; rw [hcon] at hi; omega
    calc minCount (N (t + 1)) ≤ N (t + 1) i := minCount_le _ _
      _ = N t i := hval i hine
      _ = minCount (N t) := hi
  refine ⟨hmin, ?_⟩
  ext i
  simp only [argMinSet, Finset.mem_filter, Finset.mem_univ, true_and, hmin]
  by_cases hi : i = arm t
  · rw [hi]
    have h1 : N (t + 1) (arm t) = N t (arm t) + 1 := by
      rw [h.step t (arm t), if_pos rfl]
    constructor
    · intro hc; omega
    · intro hc; omega
  · rw [hval i hi]

/-- On a step that increments a minimal arm the potential strictly increases. -/
theorem potential_lt_of_min (h : IsForcedExploration N arm g) {t : ℕ}
    (hmin : N t (arm t) = minCount (N t)) :
    potential N t < potential N (t + 1) := by
  classical
  set a : Fin k := arm t with ha
  set m : ℕ := minCount (N t) with hm
  have hval : ∀ i, i ≠ a → N (t + 1) i = N t i := by
    intro i hi; rw [h.step t i, if_neg hi, Nat.add_zero]
  have haval : N (t + 1) a = m + 1 := by rw [h.step t a, if_pos rfl, hmin]
  by_cases hsingle : (argMinSet (N t)).card = 1
  · -- the minimum rises by one
    have hother : ∀ i, i ≠ a → m < N t i := by
      intro i hi
      rcases lt_or_eq_of_le (minCount_le (N t) i) with hlt | heq
      · exact hlt
      · exfalso
        have hmem : i ∈ argMinSet (N t) := by
          simp only [argMinSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact heq.symm
        have hamem : a ∈ argMinSet (N t) := by
          simp only [argMinSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hmin
        have := Finset.card_le_one.mp (le_of_eq hsingle) i hmem a hamem
        exact hi this
    have hmin' : minCount (N (t + 1)) = m + 1 := by
      refine le_antisymm ?_ (le_minCount fun i ↦ ?_)
      · calc minCount (N (t + 1)) ≤ N (t + 1) a := minCount_le _ _
          _ = m + 1 := haval
      · by_cases hi : i = a
        · subst hi; rw [haval]
        · rw [hval i hi]; exact hother i hi
    have hc : (argMinSet (N (t + 1))).card ≤ k := card_argMinSet_le _
    have hc0 : 1 ≤ (argMinSet (N t)).card := one_le_card_argMinSet _
    rw [potential, potential, hmin', ← hm, hsingle]
    have : k * (m + 1) = k * m + k := by ring
    rw [this]
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
    omega
  · -- the minimum stays, the argmin set shrinks
    have hc2 : 2 ≤ (argMinSet (N t)).card := by
      have := one_le_card_argMinSet (N t); omega
    obtain ⟨b, hbmem, hbne⟩ : ∃ b ∈ argMinSet (N t), b ≠ a := by
      by_contra hcon
      push_neg at hcon
      have hsub : argMinSet (N t) ⊆ {a} := fun x hx ↦ by
        simp only [Finset.mem_singleton]
        exact hcon x hx
      have hcle := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hcle
      omega
    have hbval : N t b = m := by
      simpa [argMinSet] using hbmem
    have hmin' : minCount (N (t + 1)) = m := by
      refine le_antisymm ?_ (minCount_le_succ h t)
      calc minCount (N (t + 1)) ≤ N (t + 1) b := minCount_le _ _
        _ = N t b := hval b hbne
        _ = m := hbval
    -- the argmin set loses exactly `a`
    have hsub : argMinSet (N (t + 1)) = (argMinSet (N t)).erase a := by
      ext i
      simp only [argMinSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, hmin']
      by_cases hi : i = a
      · rw [hi]
        simp only [haval, ne_eq, not_true_eq_false, false_and, iff_false]
        omega
      · rw [hval i hi]
        simp [hi, ← hm]
    have hamem : a ∈ argMinSet (N t) := by
      simp only [argMinSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmin
    have hcard : (argMinSet (N (t + 1))).card = (argMinSet (N t)).card - 1 := by
      rw [hsub, Finset.card_erase_of_mem hamem]
    have hle := card_argMinSet_le (N t)
    rw [potential, potential, hmin', ← hm, hcard]
    omega

theorem potential_le_succ (h : IsForcedExploration N arm g) (t : ℕ) :
    potential N t ≤ potential N (t + 1) := by
  by_cases hmin : N t (arm t) = minCount (N t)
  · exact le_of_lt (potential_lt_of_min h hmin)
  · obtain ⟨h1, h2⟩ := step_of_not_min h hmin
    rw [potential, potential, h1, h2]

/-! ## Counting the forced steps -/

/-- The rounds among the first `t` at which the rule was forced to explore. -/
noncomputable def forcedSet (N : ℕ → Fin k → ℕ) (g : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter fun u ↦ minCount (N u) < g u

/-- **At most `Φ(t)` of the first `t` rounds were forced.** -/
theorem card_forcedSet_le (h : IsForcedExploration N arm g) (t : ℕ) :
    (forcedSet N g t).card ≤ potential N t := by
  classical
  induction t with
  | zero => simp [forcedSet, potential_zero h]
  | succ t ih =>
      have hstep : forcedSet N g (t + 1) =
          if minCount (N t) < g t then insert t (forcedSet N g t)
          else forcedSet N g t := by
        by_cases hc : minCount (N t) < g t
        · rw [if_pos hc]
          ext u
          simp only [forcedSet, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
          constructor
          · rintro ⟨hu, hu2⟩
            rcases Nat.lt_or_ge u t with h1 | h1
            · exact Or.inr ⟨h1, hu2⟩
            · exact Or.inl (by omega)
          · rintro (rfl | ⟨h1, h2⟩)
            · exact ⟨by omega, hc⟩
            · exact ⟨by omega, h2⟩
        · rw [if_neg hc]
          ext u
          simp only [forcedSet, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hu, hu2⟩
            refine ⟨?_, hu2⟩
            rcases Nat.lt_or_ge u t with h1 | h1
            · exact h1
            · exact absurd (by rw [show u = t by omega] at hu2; exact hu2) hc
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      by_cases hc : minCount (N t) < g t
      · rw [hstep, if_pos hc]
        have hnot : t ∉ forcedSet N g t := by simp [forcedSet]
        rw [Finset.card_insert_of_notMem hnot]
        have hlt : potential N t < potential N (t + 1) :=
          potential_lt_of_min h (h.forced t hc)
        omega
      · rw [hstep, if_neg hc]
        exact le_trans ih (potential_le_succ h t)

/-! ## The conclusion -/

/-- **(★).**  Every window of `k · m(t) + k` consecutive rounds before `t`
contains an unforced round, at which `g` was already at most the minimum; since
both `g` and `m` are monotone this bounds `g` at the start of the window. -/
theorem le_minCount_of_add_le (h : IsForcedExploration N arm g) (hg : Monotone g)
    {s t : ℕ} (hst : s + (k * minCount (N t) + k) ≤ t) :
    g s ≤ minCount (N t) := by
  classical
  -- the window `[s, t)` cannot be entirely forced
  have hwin : ∃ u, s ≤ u ∧ u < t ∧ ¬ (minCount (N u) < g u) := by
    by_contra hcon
    push_neg at hcon
    have hsub : Finset.Ico s t ⊆ forcedSet N g t := by
      intro u hu
      rw [Finset.mem_Ico] at hu
      simp only [forcedSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨hu.2, hcon u hu.1 hu.2⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hcard
    have hpot := le_trans (card_forcedSet_le h t) (potential_le (N := N) t)
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
    omega
  obtain ⟨u, hsu, hut, hnf⟩ := hwin
  push_neg at hnf
  calc g s ≤ g u := hg hsu
    _ ≤ minCount (N u) := hnf
    _ ≤ minCount (N t) := minCount_mono' h hut.le

/-- The quantitative form.  If `g` is monotone and "`g s ≤ M` forces `s` small",
then a small minimum forces a small round index. -/
theorem le_of_minCount_le (h : IsForcedExploration N arm g) (hg : Monotone g)
    {t M : ℕ} (hM : minCount (N t) ≤ M)
    (hlt : ∀ s, g s ≤ M → s ≤ M * M) :
    t ≤ M * M + k * M + k := by
  by_contra hcon
  push_neg at hcon
  set s : ℕ := t - (k * minCount (N t) + k) with hs
  have hkM : k * minCount (N t) + k ≤ k * M + k :=
    Nat.add_le_add_right (Nat.mul_le_mul_left k hM) k
  have hst : s + (k * minCount (N t) + k) ≤ t := by omega
  have hgs : g s ≤ minCount (N t) := le_minCount_of_add_le h hg hst
  have hsM := hlt s (le_trans hgs hM)
  omega

/-! ## The `√t` instance

With the D-Tracking threshold `g(t) = ⌊√t⌋` the bound reads
`t < (m(t) + 1)² + k m(t) + k`, i.e. `m(t) > √t − k − 1` for large `t`: every arm
is played at least of order `√t` times. -/

theorem monotone_nat_sqrt : Monotone Nat.sqrt := fun _ _ h ↦ Nat.sqrt_le_sqrt h

/-- **Garivier–Kaufmann Lemma 7, quantitatively.**  Under `√`-forced exploration
the least-played count `m(t)` satisfies `t < (m(t) + 1)² + k m(t) + k`. -/
theorem sqrt_forced_bound (h : IsForcedExploration N arm Nat.sqrt) (t : ℕ) :
    t < (minCount (N t) + 1) * (minCount (N t) + 1) + k * minCount (N t) + k := by
  set m : ℕ := minCount (N t) with hm
  rcases Nat.lt_or_ge t (k * m + k) with hsmall | hbig
  · nlinarith [Nat.zero_le (m * m)]
  · set s : ℕ := t - (k * m + k) with hs
    have hst : s + (k * m + k) ≤ t := by omega
    have hgs : Nat.sqrt s ≤ m := le_minCount_of_add_le h monotone_nat_sqrt hst
    have hslt : s < (m + 1) * (m + 1) := by
      by_contra hcon
      push_neg at hcon
      have : m + 1 ≤ Nat.sqrt s := Nat.le_sqrt.mpr hcon
      omega
    omega

end BanditAlgorithm

theorem _root_.solution {k : ℕ} (hk : 0 < k) (N : ℕ → Fin k → ℕ) (arm : ℕ → Fin k)
    (m : ℕ → ℕ) (hmle : ∀ t i, m t ≤ N t i) (hmatt : ∀ t, ∃ i, N t i = m t)
    (hinit : ∀ i, N 0 i = 0)
    (hstep : ∀ t i, N (t + 1) i = N t i + (if i = arm t then 1 else 0))
    (hforced : ∀ t, m t < Nat.sqrt t → N t (arm t) = m t) (t : ℕ) :
    t < (m t + 1) * (m t + 1) + k * m t + k := by
  haveI : NeZero k := ⟨by omega⟩
  have hm : ∀ s, m s = BanditAlgorithm.minCount (N s) := by
    intro s
    refine le_antisymm (BanditAlgorithm.le_minCount (hmle s)) ?_
    obtain ⟨i, hi⟩ := hmatt s
    calc BanditAlgorithm.minCount (N s) ≤ N s i := BanditAlgorithm.minCount_le _ _
      _ = m s := hi
  have hfe : BanditAlgorithm.IsForcedExploration N arm Nat.sqrt :=
    { init := hinit
      step := hstep
      forced := fun s hs ↦ by
        rw [← hm s]; exact hforced s (by rwa [hm s]) }
  have := BanditAlgorithm.sqrt_forced_bound hfe t
  rwa [← hm t] at this
