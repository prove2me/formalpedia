-- Prove2me | solution 1 for Freiman.padded_copies_window_cases
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:20:53.784574+00:00
-- url     : https://prove2.me/submissions/cbc8ce0f-5dc6-4464-8d3b-398610791ba7

import Definitions.Def_Freiman_paddedCopies

open Freiman

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem start_succ (j : ℕ) :
    paddedStart (j + 1) = paddedStart j + 4 * j + 1 := by
  cases j with
  | zero => norm_num [paddedStart]
  | succ j =>
    have h₁ : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    have h₂ : 2 * (j + 1 + 1) - 1 = 2 * j + 3 := by omega
    simp only [paddedStart, h₁, h₂]
    ring

private theorem start_strict : StrictMono paddedStart := by
  apply strictMono_nat_of_lt_succ
  intro j
  change paddedStart j < paddedStart (j + 1)
  rw [start_succ]
  omega

private theorem block_at (n : ℕ) :
    ∃ j : ℕ, paddedStart j ≤ n ∧ n < paddedStart (j + 1) := by
  induction n with
  | zero => exact ⟨0, by norm_num [paddedStart], by norm_num [paddedStart]⟩
  | succ n ih =>
    obtain ⟨j, hj₀, hj₁⟩ := ih
    by_cases h : n + 1 < paddedStart (j + 1)
    · exact ⟨j, by omega, h⟩
    · refine ⟨j + 1, by omega, ?_⟩
      rw [start_succ (j + 1)]
      omega

private theorem copy_offset (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+)
    (hcopy : PaddedCopies a b d) (j : ℕ) (u : ℤ)
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ ((4 * j : ℕ) : ℤ)) :
    b ((paddedStart j : ℤ) + u) = a j (u - ((2 * j : ℕ) : ℤ)) := by
  have hu : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu₀
  have hn : u.toNat ≤ 4 * j := by omega
  simpa only [Nat.cast_add, hu] using hcopy.2 j u.toNat hn

private theorem pad_position (a : ℕ → ℤ → ℕ+) (d : ℕ+)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d)
    (j : ℕ) (u : ℤ) (h : u < (j : ℤ) ∨ ((3 * j : ℕ) : ℤ) < u) :
    a j (u - ((2 * j : ℕ) : ℤ)) = d := by
  apply hpad
  have he := Int.natCast_natAbs (u - ((2 * j : ℕ) : ℤ))
  rcases h with h | h
  · rw [abs_of_neg (by omega)] at he
    omega
  · rw [abs_of_pos (by omega)] at he
    omega

private theorem left_join (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+)
    (hcopy : PaddedCopies a b d)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d)
    (m x R : ℕ) (hm : 2 * R ≤ m) (hx : x < R)
    (k : ℤ) (hk₀ : -(R : ℤ) ≤ k) (hk₁ : k ≤ (R : ℤ)) :
    b ((paddedStart (m + 1) : ℤ) + (x : ℤ) + k) = d := by
  by_cases hu : 0 ≤ (x : ℤ) + k
  · have hc := copy_offset a b d hcopy (m + 1) ((x : ℤ) + k) hu (by omega)
    have hpad' := pad_position a d hpad (m + 1) ((x : ℤ) + k)
      (Or.inl (by omega))
    simpa only [add_assoc] using hc.trans hpad'
  · have hv₀ : (0 : ℤ) ≤ ((4 * m + 1 : ℕ) : ℤ) + (x : ℤ) + k := by omega
    have hv₁ : ((4 * m + 1 : ℕ) : ℤ) + (x : ℤ) + k ≤ ((4 * m : ℕ) : ℤ) := by omega
    have hc := copy_offset a b d hcopy m
      (((4 * m + 1 : ℕ) : ℤ) + (x : ℤ) + k) hv₀ hv₁
    have hpad' := pad_position a d hpad m
      (((4 * m + 1 : ℕ) : ℤ) + (x : ℤ) + k) (Or.inr (by omega))
    have hs : (paddedStart (m + 1) : ℤ) =
        (paddedStart m : ℤ) + ((4 * m + 1 : ℕ) : ℤ) := by
      exact_mod_cast (show paddedStart (m + 1) = paddedStart m + (4 * m + 1) by
        rw [start_succ]
        omega)
    simpa only [hs, add_assoc] using hc.trans hpad'

private theorem right_join (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+)
    (hcopy : PaddedCopies a b d)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d)
    (j x R : ℕ) (hj : 2 * R ≤ j) (hx : x ≤ 4 * j) (hcross : 4 * j < x + R)
    (k : ℤ) (hk₀ : -(R : ℤ) ≤ k) (hk₁ : k ≤ (R : ℤ)) :
    b ((paddedStart j : ℤ) + (x : ℤ) + k) = d := by
  by_cases hu : (x : ℤ) + k ≤ ((4 * j : ℕ) : ℤ)
  · have hc := copy_offset a b d hcopy j ((x : ℤ) + k) (by omega) hu
    have hpad' := pad_position a d hpad j ((x : ℤ) + k) (Or.inr (by omega))
    simpa only [add_assoc] using hc.trans hpad'
  · have hv₀ : (0 : ℤ) ≤ (x : ℤ) + k - ((4 * j + 1 : ℕ) : ℤ) := by omega
    have hv₁ : (x : ℤ) + k - ((4 * j + 1 : ℕ) : ℤ) ≤ ((4 * (j + 1) : ℕ) : ℤ) := by omega
    have hc := copy_offset a b d hcopy (j + 1)
      ((x : ℤ) + k - ((4 * j + 1 : ℕ) : ℤ)) hv₀ hv₁
    have hpad' := pad_position a d hpad (j + 1)
      ((x : ℤ) + k - ((4 * j + 1 : ℕ) : ℤ)) (Or.inl (by omega))
    have hs : (paddedStart (j + 1) : ℤ) =
        (paddedStart j : ℤ) + ((4 * j + 1 : ℕ) : ℤ) := by
      exact_mod_cast (show paddedStart (j + 1) = paddedStart j + (4 * j + 1) by
        rw [start_succ]
        omega)
    have he : (paddedStart (j + 1) : ℤ) +
        ((x : ℤ) + k - ((4 * j + 1 : ℕ) : ℤ)) =
        (paddedStart j : ℤ) + (x : ℤ) + k := by
      rw [hs]
      ring
    simpa only [he] using hc.trans hpad'

theorem solution (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+)
    (hcopy : PaddedCopies a b d)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d) (R J : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∃ j : ℕ, J ≤ j ∧ ∃ i : ℤ,
        ∀ k : ℤ, -(R : ℤ) ≤ k → k ≤ (R : ℤ) → b ((n : ℤ) + k) = a j (i + k)) ∨
      (∀ k : ℤ, -(R : ℤ) ≤ k → k ≤ (R : ℤ) → b ((n : ℤ) + k) = d) := by
  let L := max J (2 * R + 1)
  refine ⟨paddedStart L, ?_⟩
  intro n hn
  obtain ⟨j, hj₀, hj₁⟩ := block_at n
  have hLj : L ≤ j := by
    by_contra h
    have hs := start_strict.monotone (show j + 1 ≤ L by omega)
    omega
  have hJj : J ≤ j := (le_max_left _ _).trans hLj
  have hRj : 2 * R + 1 ≤ j := (le_max_right _ _).trans hLj
  let x := n - paddedStart j
  have hnx : n = paddedStart j + x := by omega
  have hx : x ≤ 4 * j := by
    rw [start_succ] at hj₁
    omega
  have hnz : (n : ℤ) = (paddedStart j : ℤ) + (x : ℤ) := by exact_mod_cast hnx
  by_cases hleft : R ≤ x
  · by_cases hright : x + R ≤ 4 * j
    · left
      refine ⟨j, hJj, (x : ℤ) - ((2 * j : ℕ) : ℤ), ?_⟩
      intro k hk₀ hk₁
      have hc := copy_offset a b d hcopy j ((x : ℤ) + k) (by omega) (by omega)
      rw [hnz, add_assoc]
      refine hc.trans ?_
      congr 1
      ring
    · right
      intro k hk₀ hk₁
      rw [hnz]
      exact right_join a b d hcopy hpad j x R (by omega) hx (by omega) k hk₀ hk₁
  · right
    cases j with
    | zero => omega
    | succ m =>
      intro k hk₀ hk₁
      rw [hnz]
      exact left_join a b d hcopy hpad m x R (by omega) (by omega) k hk₀ hk₁
