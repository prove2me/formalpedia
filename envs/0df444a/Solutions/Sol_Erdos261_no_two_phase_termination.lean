-- Prove2me | solution 1 for Erdos261.no_two_phase_termination
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:08:18.924968+00:00
-- url     : https://prove2.me/submissions/28458337-6eff-4880-9ec2-3f6e41253838

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset


namespace E261R
open Erdos261

/-- Borwein–Loring numbers `c j = 2^(j+1) - j - 2`. -/
def cBL (j : ℕ) : ℕ := 2 ^ (j + 1) - j - 2

lemma two_pow_ge (j : ℕ) : j + 2 ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; omega

lemma cBL_succ (j : ℕ) : cBL (j + 1) = 2 * cBL j + j + 1 := by
  unfold cBL
  have := two_pow_ge j
  rw [show j + 1 + 1 = (j + 1) + 1 by rfl, pow_succ]
  omega

lemma cBL_mono {i j : ℕ} (h : i ≤ j) : cBL i ≤ cBL j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => rw [cBL_succ]; omega

lemma cBL_add (j : ℕ) : cBL j + j + 2 = 2 ^ (j + 1) := by
  unfold cBL; have := two_pow_ge j; omega

/-- Basic window: `0 ≤ g_j ≤ n + j`. -/
lemma greedy_window (n j : ℕ) : 0 ≤ greedy n j ∧ greedy n j ≤ ((n + j : ℕ) : ℤ) := by
  induction j with
  | zero => simp [greedy]
  | succ j ih =>
    simp only [greedy]
    push_cast at ih ⊢
    split_ifs with h <;> constructor <;> omega

/-- The GPT step map `(N,R) ↦ (N+1, 2R mod (N+1))` iterated from `(n,n)` is exactly the greedy carry. -/
def step (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + 1, (2 * p.2) % (p.1 + 1))

theorem step_iter_eq_greedy (n j : ℕ) :
    step^[j] (n, n) = (n + j, (greedy n j).toNat) := by
  induction j with
  | zero => simp [greedy]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    have hw := greedy_window n j
    simp only [step, greedy, Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    set g := greedy n j with hg
    obtain ⟨k, hk⟩ : ∃ k : ℕ, g = k := ⟨g.toNat, (Int.toNat_of_nonneg hw.1).symm⟩
    rw [hk] at hw ⊢
    simp only [Int.toNat_natCast]
    push_cast at hw
    have hk' : k ≤ n + j := by exact_mod_cast hw.2
    split_ifs with h
    · have h' : n + j + 1 ≤ 2 * k := by exact_mod_cast h
      rw [show (2 : ℤ) * k - ((n + j + 1 : ℕ) : ℤ) = ((2 * k - (n + j + 1) : ℕ) : ℤ) by push_cast [h']; ring,
        Int.toNat_natCast]
      rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]
    · have h' : 2 * k < n + j + 1 := by push Not at h; exact_mod_cast h
      rw [show (2 : ℤ) * k = ((2 * k : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast,
        Nat.mod_eq_of_lt h']

/-- A1c: closed form of the first (subtracting) phase. -/
theorem first_phase (n j : ℕ) (h : cBL j ≤ n) : ∀ i ≤ j, greedy n i = (n : ℤ) - cBL i := by
  intro i hi
  induction i with
  | zero => simp [greedy, cBL]
  | succ i ih =>
    have ih := ih (by omega)
    have hc : cBL (i + 1) ≤ n := le_trans (cBL_mono hi) h
    rw [cBL_succ] at hc
    simp only [greedy, ih, cBL_succ]
    push_cast
    rw [if_pos (by omega)]
    ring

/-- A1c: step `i` of the greedy carry subtracts iff `n ≥ c (i+1)`, as long as `c i ≤ n`. -/
theorem first_phase_step (n i : ℕ) (h : cBL i ≤ n) :
    ((n + i + 1 : ℕ) : ℤ) ≤ 2 * greedy n i ↔ cBL (i + 1) ≤ n := by
  rw [first_phase n i h i le_rfl, cBL_succ]; push_cast; omega

/-- A1c combined. -/
theorem first_phase_full (n j : ℕ) (h : cBL j ≤ n) :
    ∀ i ≤ j, greedy n i = (n : ℤ) - cBL i ∧
      (((n + i + 1 : ℕ) : ℤ) ≤ 2 * greedy n i ↔ cBL (i + 1) ≤ n) := fun i hi =>
  ⟨first_phase n j h i hi, first_phase_step n i (le_trans (cBL_mono hi) h)⟩

/-- A2, Diophantine core. -/
theorem no_second_phase_dioph (j r t : ℕ) (ht : 1 ≤ t) :
    r * (2 ^ (t + 1) - 1) ≠ 2 ^ (j + 1) + t - 1 := by
  intro hEq
  set M := 2 ^ (t + 1) - 1 with hM
  have hpt : t + 2 ≤ 2 ^ (t + 1) := two_pow_ge t
  have hlt : t < 2 ^ t := Nat.lt_two_pow_self
  have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
  have hM3 : 3 ≤ M := by omega
  have h1 : 2 ^ (t + 1) % M = 1 := by
    rw [show 2 ^ (t + 1) = M + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  set e := (j + 1) % (t + 1)
  have he : e ≤ t := by have := Nat.mod_lt (j + 1) (show 0 < t + 1 by omega); omega
  have hsplit : 2 ^ (j + 1) = (2 ^ (t + 1)) ^ ((j + 1) / (t + 1)) * 2 ^ e := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hmod : 2 ^ (j + 1) % M = 2 ^ e % M := by
    rw [hsplit, Nat.mul_mod, Nat.pow_mod, h1, one_pow, Nat.one_mod_eq_one.mpr (by omega), one_mul,
      Nat.mod_mod]
  have he2 : 2 ^ e ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) he
  have hsmall : 2 ^ e + t - 1 < M := by omega
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hl : (r * M) % M = 0 := Nat.mul_mod_left r M
  rw [hEq] at hl
  have : (2 ^ (j + 1) + t - 1) % M = (2 ^ e + t - 1) % M := by
    have a1 : 2 ^ (j + 1) + t - 1 = 2 ^ (j + 1) + (t - 1) := by omega
    have a2 : 2 ^ e + t - 1 = 2 ^ e + (t - 1) := by omega
    rw [a1, a2, Nat.add_mod, hmod, ← Nat.add_mod]
  rw [this, Nat.mod_eq_of_lt hsmall] at hl
  omega

/-- A2, full statement: if `c j < n < c (j+1)` (so `n` is not a Borwein–Loring number) and the
`t` steps after the first phase are all doubling steps, then the greedy carry is nonzero at every
time `i ≤ j + t + 1`; i.e. the orbit cannot reach `0` during the subtracting phase, the doubling
phase, or at the first subtraction after it. -/
theorem no_two_phase_termination (n j t : ℕ) (h1 : cBL j < n) (h2 : n < cBL (j + 1))
    (hdbl : ∀ s < t, greedy n (j + s + 1) = 2 * greedy n (j + s)) :
    ∀ i ≤ j + t + 1, greedy n i ≠ 0 := by
  have hfp := first_phase n j h1.le
  set r : ℕ := n - cBL j with hr
  have hr1 : 1 ≤ r := by omega
  have hgj : greedy n j = r := by rw [hfp j le_rfl]; push_cast [hr, h1.le]; ring
  have hdoub : ∀ s ≤ t, greedy n (j + s) = 2 ^ s * (r : ℤ) := by
    intro s hs
    induction s with
    | zero => simpa using hgj
    | succ s ih =>
      rw [show j + (s + 1) = j + s + 1 by ring, hdbl s (by omega), ih (by omega), pow_succ]; ring
  have hcj := cBL_add j
  intro i hi
  rcases Nat.lt_or_ge i (j + 1) with hij | hij
  · rw [hfp i (by omega)]
    have := cBL_mono (show i ≤ j by omega); omega
  rcases Nat.lt_or_ge i (j + t + 1) with hit | hit
  · obtain ⟨s, rfl⟩ : ∃ s, i = j + s := ⟨i - j, by omega⟩
    rw [hdoub s (by omega)]; positivity
  have hi' : i = j + t + 1 := by omega
  subst hi'
  have hg := hdoub t le_rfl
  simp only [greedy]
  rw [hg]
  split_ifs with hs
  · -- subtract step: value 2^(t+1) r - (n+j+t+1)
    intro h0
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      have h' : (2 : ℤ) * r = ((n + j + 1 : ℕ) : ℤ) := by push_cast at h0 ⊢; simp at h0; linarith
      have hc1 := cBL_succ j
      have : 2 * r = n + j + 1 := by exact_mod_cast h'
      omega
    · apply no_second_phase_dioph j r t htpos
      have hp1 : 1 ≤ 2 ^ (t + 1) := Nat.one_le_two_pow
      have h' : ((2 ^ (t + 1) * r : ℕ) : ℤ) = ((n + (j + t) + 1 : ℕ) : ℤ) := by
        push_cast at h0 ⊢; rw [pow_succ]; linarith
      have h'' : 2 ^ (t + 1) * r = n + (j + t) + 1 := by exact_mod_cast h'
      have hn : n = cBL j + r := by omega
      rw [Nat.mul_sub, mul_one, mul_comm]
      omega
  · intro h0
    have : (2 : ℤ) * (2 ^ t * r) ≠ 0 := by positivity
    exact this h0

/-- A1b: on a non-terminating greedy orbit, doubling steps and subtracting steps both occur
infinitely often. -/
theorem phase_types_infinite (n : ℕ) (hnt : ∀ k, greedy n k ≠ 0) :
    (∀ K, ∃ k ≥ K, 2 * greedy n k < ((n + k + 1 : ℕ) : ℤ)) ∧
    (∀ K, ∃ k ≥ K, ((n + k + 1 : ℕ) : ℤ) ≤ 2 * greedy n k) := by
  have hpos : ∀ k, 1 ≤ greedy n k := fun k => by
    have := (greedy_window n k).1; have := hnt k; omega
  have exp_beats : ∀ a : ℕ, ∃ t : ℕ, a + t + 2 ≤ 2 ^ (t + 1) := fun a =>
    ⟨a, by have : a < 2 ^ a := Nat.lt_two_pow_self
           rw [pow_succ]; omega⟩
  constructor
  · -- if eventually always subtracting, the deficit `N - R` grows like `2^t`
    intro K
    by_contra hc
    push Not at hc
    have hdef : ∀ t, ((n + K + t : ℕ) : ℤ) - greedy n (K + t) + 2 ≥ 2 ^ t * 2 := by
      intro t
      induction t with
      | zero =>
        have := (greedy_window n (K + 0)).2; simp at this ⊢; linarith
      | succ t ih =>
        have h := hc (K + t) (by omega)
        have e : greedy n (K + (t + 1)) = 2 * greedy n (K + t) - ((n + (K + t) + 1 : ℕ) : ℤ) := by
          rw [show K + (t + 1) = K + t + 1 by ring]; simp only [greedy]
          rw [if_pos (by push_cast at h ⊢; linarith)]
        rw [e, pow_succ]; push_cast at ih ⊢; nlinarith
    obtain ⟨t, ht⟩ := exp_beats (n + K)
    have h1 := hdef t
    have h2 := hpos (K + t)
    have : (n + K + t : ℤ) + 2 ≤ 2 ^ (t + 1) := by exact_mod_cast ht
    push_cast at h1
    rw [pow_succ] at this
    linarith
  · intro K
    by_contra hc
    push Not at hc
    have hgrow : ∀ t, greedy n (K + t) ≥ 2 ^ t := by
      intro t
      induction t with
      | zero => simpa using hpos K
      | succ t ih =>
        have h := hc (K + t) (by omega)
        rw [show K + (t + 1) = K + t + 1 by ring]; simp only [greedy]
        rw [if_neg (by push_cast at h ⊢; linarith), pow_succ]; linarith
    obtain ⟨t, ht⟩ := exp_beats (n + K)
    have h1 := hgrow t
    have h2 := hc (K + t) (by omega)
    have : (n + K + t : ℤ) + 2 ≤ 2 ^ (t + 1) := by exact_mod_cast ht
    push_cast at h2
    rw [pow_succ] at this
    linarith

end E261R


namespace Erdos261

theorem no_two_phase_termination (n j t : ℕ) (h1 : 2 ^ (j + 1) - j - 2 < n) (h2 : n < 2 ^ (j + 1 + 1) - (j + 1) - 2)
    (hdbl : ∀ s < t, greedy n (j + s + 1) = 2 * greedy n (j + s)) :
    ∀ i ≤ j + t + 1, greedy n i ≠ 0 :=
  E261R.no_two_phase_termination n j t h1 h2 hdbl

end Erdos261

open Erdos261 in
theorem solution (n j t : ℕ) (h1 : 2 ^ (j + 1) - j - 2 < n) (h2 : n < 2 ^ (j + 1 + 1) - (j + 1) - 2)
    (hdbl : ∀ s < t, greedy n (j + s + 1) = 2 * greedy n (j + s)) :
    ∀ i ≤ j + t + 1, greedy n i ≠ 0 :=
  Erdos261.no_two_phase_termination n j t h1 h2 hdbl

#print axioms solution
