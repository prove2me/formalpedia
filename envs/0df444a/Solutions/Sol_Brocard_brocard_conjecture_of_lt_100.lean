-- Prove2me | solution 1 for Brocard.brocard_conjecture_of_lt_100
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-01T00:52:41.575366+00:00
-- url     : https://prove2.me/submissions/4e470f82-4b0e-4afb-84a7-3738ab07a272

import Mathlib
open Finset Filter

namespace BrocardSmall

/-- Trial division: `true` only if no `m` with `d ≤ m`, `m*m ≤ n` divides `n`
(returns `false` when fuel runs out). -/
def tdivOK (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, f + 1 => if n < d * d then true else if n % d = 0 then false else tdivOK n (d + 1) f

/-- Divisor search: `true` only if some `m` with `d ≤ m`, `m*m ≤ n` divides `n`. -/
def hasDiv (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, f + 1 => if n < d * d then false else if n % d = 0 then true else hasDiv n (d + 1) f

def primeB (n : ℕ) : Bool := 2 ≤ n && tdivOK n 2 n

theorem tdivOK_sound (n : ℕ) : ∀ f d, tdivOK n d f = true →
    ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro f
  induction f with
  | zero => intro d h; simp [tdivOK] at h
  | succ f ih =>
    intro d h m hdm hmn hdvd
    simp only [tdivOK] at h
    split_ifs at h with h1 h2
    · exact absurd (lt_of_lt_of_le h1 (le_trans (Nat.mul_le_mul hdm hdm) hmn)) (lt_irrefl _)
    · rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
      · exact h2 (Nat.eq_zero_of_dvd_of_lt (by omega) (by omega) |> fun _ => Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih (d + 1) h m hlt hmn hdvd

theorem primeB_sound (n : ℕ) (h : primeB n = true) : n.Prime := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, h⟩ := h
  by_contra hp
  have hn1 : n ≠ 1 := by omega
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  have hmin2 : 2 ≤ n.minFac := (Nat.minFac_prime hn1).two_le
  exact tdivOK_sound n n 2 h n.minFac hmin2 (by nlinarith [hsq]) (Nat.minFac_dvd n)

theorem hasDiv_sound (n : ℕ) : ∀ f d, 2 ≤ d → hasDiv n d f = true → ¬ n.Prime := by
  intro f
  induction f with
  | zero => intro d _ h; simp [hasDiv] at h
  | succ f ih =>
    intro d hd h hp
    simp only [hasDiv] at h
    split_ifs at h with h1 h2
    · have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h2
      rcases hp.eq_one_or_self_of_dvd d hdvd with h3 | h3
      · omega
      · subst h3; nlinarith
    · exact ih (d + 1) (by omega) h hp

/-- `true` only if none of `a+1, …, a+len` is prime. -/
def noPrime (a : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => hasDiv (a + 1 + len) 2 (a + 1 + len) && noPrime a len

theorem noPrime_sound (a : ℕ) : ∀ len, noPrime a len = true →
    ∀ x, a < x → x < a + 1 + len → ¬ x.Prime := by
  intro len
  induction len with
  | zero => intro _ x h1 h2; omega
  | succ len ih =>
    intro h x h1 h2
    simp only [noPrime, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge x (a + 1 + len) with hx | hx
    · exact ih h.2 x h1 hx
    · have : x = a + 1 + len := by omega
      subst this
      exact hasDiv_sound _ _ 2 le_rfl h.1

/-- Number of `primeB` hits among `a+1, …, a+m`. -/
def cntB (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => cntB a m + if primeB (a + 1 + m) then 1 else 0

theorem cntB_le (a : ℕ) : ∀ m, cntB a m ≤ ((Ioo a (a + 1 + m)).filter Nat.Prime).card := by
  intro m
  induction m with
  | zero => simp [cntB]
  | succ m ih =>
    have hins : Ioo a (a + 1 + (m + 1)) = insert (a + 1 + m) (Ioo a (a + 1 + m)) := by
      ext x; simp only [mem_Ioo, mem_insert]; omega
    have hnot : a + 1 + m ∉ Ioo a (a + 1 + m) := by simp
    rw [hins, filter_insert]
    simp only [cntB]
    split_ifs with h1 h2
    · rw [card_insert_of_notMem (by simp)]; omega
    · exact absurd (primeB_sound _ h1) h2
    · simp only [add_zero]; exact ih.trans (card_le_card (subset_insert _ _))
    · omega

/-- Position (offset) right after the 4th prime found after `a` (fuel-bounded). -/
def pos4 (a : ℕ) : ℕ → ℕ → ℕ → ℕ
  | i, _, 0 => i
  | i, k, f + 1 => if 4 ≤ k then i else
      pos4 a (i + 1) (if primeB (a + 1 + i) then k + 1 else k) f

def has4 (a b : ℕ) : Bool :=
  let m := pos4 a 0 0 1000
  decide (a + 1 + m ≤ b) && decide (4 ≤ cntB a m)

theorem has4_sound (a b : ℕ) (h : has4 a b = true) :
    4 ≤ ((Ioo a b).filter Nat.Prime).card := by
  simp only [has4, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine le_trans h2 (le_trans (cntB_le a _) (card_le_card ?_))
  intro x hx
  simp only [mem_filter, mem_Ioo] at hx ⊢
  exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩

/-- Next prime after `p` found by search (fuel-bounded; correctness checked separately). -/
def nextP (p : ℕ) : ℕ → ℕ
  | 0 => p + 1
  | f + 1 => if primeB (p + 1) then p + 1 else nextP (p + 1) f

def gapOK (p q : ℕ) : Bool := decide (p < q) && primeB q && noPrime p (q - p - 1)

theorem nth_succ_of_gapOK (k p q : ℕ) (hk : Nat.nth Nat.Prime k = p) (hpr : p.Prime)
    (h : gapOK p q = true) : Nat.nth Nat.Prime (k + 1) = q := by
  simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpq, hq⟩, hno⟩ := h
  have hqp := primeB_sound q hq
  have hnp := noPrime_sound p _ hno
  have hc : Nat.count Nat.Prime p = k := by
    rw [← hk]; exact Nat.count_nth_of_infinite Nat.infinite_setOf_prime k
  have hcq : Nat.count Nat.Prime q = k + 1 := by
    have : ∀ j, p + 1 + j ≤ q → Nat.count Nat.Prime (p + 1 + j) = k + 1 := by
      intro j
      induction j with
      | zero => intro _; rw [Nat.count_succ, hc]; simp [hpr]
      | succ j ih =>
        intro hj
        rw [show p + 1 + (j + 1) = (p + 1 + j) + 1 by ring, Nat.count_succ, ih (by omega)]
        simp [hnp (p + 1 + j) (by omega) (by omega)]
    have := this (q - p - 1) (by omega)
    rwa [show p + 1 + (q - p - 1) = q by omega] at this
  rw [← hcq]; exact Nat.nth_count hqp

/-- Strict application: evaluates `n` to a numeral before passing it to `k`. -/
def force (n : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun m _ => k (m + 1)) n

theorem force_eq (n : ℕ) (k : ℕ → Bool) : force n k = k n := by
  cases n <;> rfl

/-- The main checker: starting from the prime `p`, check `fuel` consecutive
prime gaps and the four-primes property for each. -/
def chk : ℕ → ℕ → Bool
  | _, 0 => true
  | p, f + 1 =>
    force (nextP p 1000) fun q => gapOK p q && has4 (p ^ 2) (q ^ 2) && chk q f

theorem chk_sound : ∀ f k p, Nat.nth Nat.Prime k = p → chk p f = true →
    ∀ j < f, 4 ≤ ((Ioo ((k + j).nth Nat.Prime ^ 2) ((k + j + 1).nth Nat.Prime ^ 2)).filter
      Nat.Prime).card := by
  intro f
  induction f with
  | zero => intro _ _ _ _ j hj; omega
  | succ f ih =>
    intro k p hk h j hj
    simp only [chk, force_eq, Bool.and_eq_true] at h
    obtain ⟨⟨hg, h4⟩, hrest⟩ := h
    have hpr : p.Prime := hk ▸ Nat.prime_nth_prime k
    have hk1 := nth_succ_of_gapOK k p _ hk hpr hg
    rcases j with _ | j
    · simp only [Nat.add_zero]; rw [hk, hk1]; exact has4_sound _ _ h4
    · have := ih (k + 1) _ hk1 hrest j (by omega)
      rwa [show k + 1 + j = k + (j + 1) by ring] at this

theorem nth_one : Nat.nth Nat.Prime 1 = 3 :=
  nth_succ_of_gapOK 0 2 3 Nat.nth_prime_zero_eq_two Nat.prime_two (by decide +kernel)


theorem chk_ok : chk 3 99 = true := by decide +kernel

end BrocardSmall

open BrocardSmall in
theorem solution (n : ℕ) (hn : 1 ≤ n) (hn' : n < 100) :
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card := by
  have h := chk_sound 99 1 3 nth_one chk_ok (n - 1) (by omega)
  rw [show 1 + (n - 1) = n by omega] at h
  exact h
