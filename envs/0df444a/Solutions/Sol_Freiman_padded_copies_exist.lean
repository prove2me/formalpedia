-- Prove2me | solution 1 for Freiman.padded_copies_exist
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:16:27.509215+00:00
-- url     : https://prove2.me/submissions/97718d3b-dcfe-4bfb-a0af-ea1398ed078f

import Definitions.Def_Freiman_paddedCopies

open Freiman

set_option autoImplicit false

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

private theorem block_unique (n j k : ℕ)
    (hj₀ : paddedStart j ≤ n) (hj₁ : n < paddedStart (j + 1))
    (hk₀ : paddedStart k ≤ n) (hk₁ : n < paddedStart (k + 1)) : j = k := by
  by_contra hne
  have hcases : j < k ∨ k < j := by omega
  rcases hcases with h | h
  · have hm := start_strict.monotone (show j + 1 ≤ k by omega)
    omega
  · have hm := start_strict.monotone (show k + 1 ≤ j by omega)
    omega

theorem solution (a : ℕ → ℤ → ℕ+) (d : ℕ+) :
    ∃ b : ℤ → ℕ+, PaddedCopies a b d := by
  classical
  let f : ℕ → ℕ+ := fun n =>
    let j := Classical.choose (block_at n)
    a j ((n : ℤ) - (paddedStart j : ℤ) - ((2 * j : ℕ) : ℤ))
  let b : ℤ → ℕ+ := fun i => if i < 0 then d else f i.toNat
  refine ⟨b, ?_, ?_⟩
  · intro i hi
    exact if_pos hi
  · intro j k hk
    have hj₀ : paddedStart j ≤ paddedStart j + k := by omega
    have hj₁ : paddedStart j + k < paddedStart (j + 1) := by
      rw [start_succ]
      omega
    have hi := Classical.choose_spec (block_at (paddedStart j + k))
    have hidx : Classical.choose (block_at (paddedStart j + k)) = j :=
      block_unique _ _ _ hi.1 hi.2 hj₀ hj₁
    change (if ((paddedStart j + k : ℕ) : ℤ) < 0 then d else
      f (((paddedStart j + k : ℕ) : ℤ).toNat)) = _
    rw [if_neg (by omega), Int.toNat_natCast]
    dsimp only [f]
    rw [hidx]
    congr 1
    push_cast
    ring
