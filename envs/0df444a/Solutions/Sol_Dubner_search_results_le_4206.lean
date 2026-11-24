-- Prove2me | solution 1 for Dubner.search_results_le_4206
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-11-24T13:10:29.588938+00:00
-- url     : https://prove2.me/submissions/c730deb2-0e89-42a0-b7c0-c8aa937abebd

import Mathlib
import Definitions.Def_Dubner_TwinPrimes

open Dubner

namespace DubnerSearch

/-! ### Two tests the kernel can run, each used only through its soundness -/

/-- Trial division from `d` upwards, with `fuel` steps. It returns `true` only when it reaches a `d`
with `n < d * d` without having met a divisor of `n`. -/
def trial (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel + 1 =>
    if n < d * d then true
    else if n % d = 0 then false
    else trial n (d + 1) fuel

/-- A primality test: `true` implies prime. -/
def isPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && trial n 2 n

theorem prime_of_trial (n : ℕ) (hn : 2 ≤ n) :
    ∀ (fuel d : ℕ), (∀ m : ℕ, 2 ≤ m → m < d → ¬ m ∣ n) → trial n d fuel = true → Nat.Prime n := by
  intro fuel
  induction fuel with
  | zero =>
    intro d _ h
    simp [trial] at h
  | succ fuel ih =>
    intro d hd h
    unfold trial at h
    split_ifs at h with h1 h2
    · rw [Nat.prime_def_le_sqrt]
      refine ⟨hn, fun m hm2 hmsq => hd m hm2 ?_⟩
      have hmm : m * m ≤ n := Nat.le_sqrt.mp hmsq
      by_contra hlt
      have hdm : d ≤ m := Nat.le_of_not_lt hlt
      have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · refine ih (d + 1) (fun m hm2 hmlt => ?_) h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmlt with hlt | rfl
      · exact hd m hm2 hlt
      · intro hdvd
        exact h2 (Nat.mod_eq_zero_of_dvd hdvd)

theorem prime_of_isPrimeB {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  unfold isPrimeB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h2, ht⟩ := h
  have hn : 2 ≤ n := of_decide_eq_true h2
  exact prime_of_trial n hn n 2 (fun m hm2 hmlt => absurd hm2 (by omega)) ht

/-- Search for a divisor `e ≥ d` of `n` with `e * e ≤ n`, with `fuel` steps. -/
def divisorFrom (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel + 1 =>
    if n < d * d then false
    else if n % d = 0 then true
    else divisorFrom n (d + 1) fuel

/-- A compositeness test: `true` implies not prime. -/
def isCompositeB (n : ℕ) : Bool := divisorFrom n 2 n

theorem not_prime_of_divisorFrom (n : ℕ) :
    ∀ (fuel d : ℕ), 2 ≤ d → divisorFrom n d fuel = true → ¬ n.Prime := by
  intro fuel
  induction fuel with
  | zero =>
    intro d _ h
    simp [divisorFrom] at h
  | succ fuel ih =>
    intro d hd h
    unfold divisorFrom at h
    split_ifs at h with h1 h2
    · intro hp
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h2
      have hdd : d * d ≤ n := Nat.le_of_not_lt h1
      rcases hp.eq_one_or_self_of_dvd d hdvd with h' | h'
      · omega
      · rw [h'] at hdd hd
        nlinarith
    · exact ih (d + 1) (by omega) h

theorem not_prime_of_isCompositeB {n : ℕ} (h : isCompositeB n = true) : ¬ n.Prime :=
  not_prime_of_divisorFrom n n 2 (le_refl 2) h

/-! ### A decomposition exists -/

def isMidB (m : ℕ) : Bool := isPrimeB (m - 1) && isPrimeB (m + 1)

theorem isMiddleNumber_of_isMidB {m : ℕ} (h : isMidB m = true) : IsMiddleNumber m := by
  unfold isMidB at h
  rw [Bool.and_eq_true] at h
  exact ⟨prime_of_isPrimeB h.1, prime_of_isPrimeB h.2⟩

/-- Looks for `m₁ = m, m + 6, m + 12, …` with `m₁` and `N - m₁` passing the middle-number test and
`N - m₁ > 4`. -/
def findMid (N : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | m, fuel + 1 =>
    if N ≤ m + 4 then false
    else if isMidB m && isMidB (N - m) then true
    else findMid N (m + 6) fuel

theorem exists_of_findMid (N : ℕ) :
    ∀ (fuel m : ℕ), 4 < m → findMid N m fuel = true →
      ∃ m₁ m₂ : ℕ, 4 < m₁ ∧ 4 < m₂ ∧ IsMiddleNumber m₁ ∧ IsMiddleNumber m₂ ∧ N = m₁ + m₂ := by
  intro fuel
  induction fuel with
  | zero =>
    intro m _ h
    simp [findMid] at h
  | succ fuel ih =>
    intro m hm h
    unfold findMid at h
    split_ifs at h with h1 h2
    · rw [Bool.and_eq_true] at h2
      exact ⟨m, N - m, hm, by omega, isMiddleNumber_of_isMidB h2.1,
        isMiddleNumber_of_isMidB h2.2, by omega⟩
    · exact ih (m + 6) (by omega) h

/-! ### No decomposition exists -/

/-- For a first term `m`, one of the four numbers `m ± 1`, `(N - m) ± 1` has a proper divisor. -/
def blocked (N m : ℕ) : Bool :=
  isCompositeB (m - 1) || isCompositeB (m + 1) ||
    isCompositeB (N - m - 1) || isCompositeB (N - m + 1)

/-- Every first term `m₁ ≥ m` with `N - m₁ > 4` is blocked. -/
def noSol (N : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | m, fuel + 1 =>
    if N ≤ m + 4 then true
    else blocked N m && noSol N (m + 1) fuel

theorem false_of_noSol (N : ℕ) :
    ∀ (fuel m : ℕ), noSol N m fuel = true →
      ∀ m₁ m₂ : ℕ, m ≤ m₁ → 4 < m₂ → IsMiddleNumber m₁ → IsMiddleNumber m₂ → N = m₁ + m₂ →
        False := by
  intro fuel
  induction fuel with
  | zero =>
    intro m h
    simp [noSol] at h
  | succ fuel ih =>
    intro m h m₁ m₂ hm hm2 h1 h2 hsum
    unfold noSol at h
    split_ifs at h with hle
    · omega
    · rw [Bool.and_eq_true] at h
      obtain ⟨hb, hrest⟩ := h
      rcases Nat.eq_or_lt_of_le hm with heq | hlt
      · rw [← heq] at h1 hsum
        unfold blocked at hb
        simp only [Bool.or_eq_true] at hb
        have e2 : N - m - 1 = m₂ - 1 := by omega
        have e3 : N - m + 1 = m₂ + 1 := by omega
        rcases hb with ((hb | hb) | hb) | hb
        · exact not_prime_of_isCompositeB hb h1.1
        · exact not_prime_of_isCompositeB hb h1.2
        · rw [e2] at hb
          exact not_prime_of_isCompositeB hb h2.1
        · rw [e3] at hb
          exact not_prime_of_isCompositeB hb h2.2
      · exact ih (m + 1) hrest m₁ m₂ (by omega) hm2 h1 h2 hsum

/-! ### The finite check -/

def exceptions : List ℕ := [96, 402, 516, 786, 906, 1116, 1146, 1266, 1356, 3246, 4206]

/-- For an exception, no decomposition; for any other `N`, a decomposition. -/
def checkOne (N : ℕ) : Bool :=
  if exceptions.contains N then noSol N 5 N else findMid N 6 N

/-- `checkOne` on the `c` numbers `N, N + 6, …`. -/
def checkAll : ℕ → ℕ → Bool
  | _, 0 => true
  | N, c + 1 => checkOne N && checkAll (N + 6) c

theorem checkAll_spec :
    ∀ (c N : ℕ), checkAll N c = true → ∀ i : ℕ, i < c → checkOne (N + 6 * i) = true := by
  intro c
  induction c with
  | zero =>
    intro N _ i hi
    omega
  | succ c ih =>
    intro N h i hi
    unfold checkAll at h
    rw [Bool.and_eq_true] at h
    rcases i with _ | j
    · simpa using h.1
    · have hj := ih (N + 6) h.2 j (by omega)
      have e : N + 6 * (j + 1) = N + 6 + 6 * j := by ring
      rw [e]
      exact hj

/-- The `700` multiples of `6` from `12` to `4206`. -/
theorem checkAll_ok : checkAll 12 700 = true := by
  decide +kernel

theorem contains_iff (N : ℕ) :
    exceptions.contains N = true ↔
      N ∈ ({96, 402, 516, 786, 906, 1116, 1146, 1266, 1356, 3246, 4206} : Finset ℕ) := by
  simp [exceptions]

end DubnerSearch

open DubnerSearch in
/-- Dubner's search results, for the multiples of `6` from `12` to `4206`: the eleven listed numbers
are exactly those that are not a sum of two middle numbers greater than `4`. -/
theorem solution :
    ∀ N : ℕ, 6 ∣ N → 6 < N → N ≤ 4206 →
      ((¬ ∃ m₁ m₂ : ℕ, 4 < m₁ ∧ 4 < m₂ ∧ IsMiddleNumber m₁ ∧ IsMiddleNumber m₂ ∧ N = m₁ + m₂) ↔
        N ∈ ({96, 402, 516, 786, 906, 1116, 1146, 1266, 1356, 3246, 4206} : Finset ℕ)) := by
  intro N h6 hN6 hN
  obtain ⟨k, rfl⟩ := h6
  have hbit := checkAll_spec 700 12 checkAll_ok (k - 2) (by omega)
  have hNeq : 12 + 6 * (k - 2) = 6 * k := by omega
  rw [hNeq] at hbit
  rw [← contains_iff]
  unfold checkOne at hbit
  by_cases hex : exceptions.contains (6 * k) = true
  · rw [if_pos hex] at hbit
    refine ⟨fun _ => hex, fun _ hsol => ?_⟩
    obtain ⟨m₁, m₂, hm1, hm2, h1, h2, hsum⟩ := hsol
    exact false_of_noSol (6 * k) (6 * k) 5 hbit m₁ m₂ (by omega) hm2 h1 h2 hsum
  · rw [if_neg hex] at hbit
    refine ⟨fun hno => absurd (exists_of_findMid (6 * k) (6 * k) 6 (by omega) hbit) hno,
      fun h => absurd h hex⟩
