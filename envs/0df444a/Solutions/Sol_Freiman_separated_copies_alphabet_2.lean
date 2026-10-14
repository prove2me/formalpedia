-- Prove2me | solution 2 for Freiman.separated_copies_alphabet
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-10T14:53:08.527929+00:00
-- url     : https://prove2.me/submissions/bbcae8e4-ce4b-4ea0-8698-e7c502e60a6d

import Definitions.Def_Freiman_wordRealization

open Freiman

namespace SeparatedAlphabetAux

/-- Consecutive blocks start `2(N+j)+2` apart: a window of `2(N+j)+1` digits
followed by one separator. -/
private lemma copyStart_succ (N j : ℕ) :
    copyStart N (j + 1) = copyStart N j + 2 * (N + j) + 2 := by
  unfold copyStart; ring

private lemma le_copyStart (N j : ℕ) : j ≤ copyStart N j := by
  unfold copyStart
  calc j = j * 1 := by ring
    _ ≤ j * (2 * N + j + 1) := Nat.mul_le_mul_left j (by omega)

/-- The blocks together with their separators tile `ℕ`. -/
private lemma exists_slot (N i : ℕ) :
    ∃ j, copyStart N j ≤ i ∧ i < copyStart N j + 2 * (N + j) + 2 := by
  classical
  have hP0 : copyStart N 0 ≤ i := by simp [copyStart]
  set j₀ := Nat.findGreatest (fun j => copyStart N j ≤ i) i with hj₀
  have hle : copyStart N j₀ ≤ i := by
    rw [hj₀]
    exact Nat.findGreatest_spec (P := fun j => copyStart N j ≤ i) (Nat.zero_le i) hP0
  have hgt : ¬ (copyStart N (j₀ + 1) ≤ i) := by
    by_cases hsucc : j₀ + 1 ≤ i
    · exact Nat.findGreatest_is_greatest (P := fun j => copyStart N j ≤ i)
        (by rw [← hj₀]; omega) hsucc
    · intro hcon
      have := le_copyStart N (j₀ + 1)
      omega
  rw [copyStart_succ] at hgt
  exact ⟨j₀, hle, by omega⟩

end SeparatedAlphabetAux

open SeparatedAlphabetAux in
theorem solution (a b : ℤ → ℕ+) (N : ℕ) (hcopy : SeparatedCopies a b N)
    (ha : HasFiniteAlphabet a) : HasFiniteAlphabet b := by
  obtain ⟨M, hM⟩ := ha
  obtain ⟨hneg, hblock, hsep⟩ := hcopy
  refine ⟨max M 2, ?_⟩
  intro i
  rcases lt_or_ge i 0 with hi | hi
  · rw [hneg i hi]; exact le_max_right _ _
  · have hik : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi
    obtain ⟨j, h1, h2⟩ := exists_slot N i.toNat
    rcases le_or_gt (i.toNat - copyStart N j) (2 * (N + j)) with hkle | hkgt
    · have hb := hblock j (i.toNat - copyStart N j) hkle
      have hidx : ((copyStart N j + (i.toNat - copyStart N j) : ℕ) : ℤ) = i := by
        have : copyStart N j + (i.toNat - copyStart N j) = i.toNat := by omega
        rw [this]; exact hik
      rw [hidx] at hb
      rw [hb]
      exact le_trans (hM _) (le_max_left _ _)
    · have hb := hsep j
      have hidx : ((copyStart N j + 2 * (N + j) + 1 : ℕ) : ℤ) = i := by
        have : copyStart N j + 2 * (N + j) + 1 = i.toNat := by omega
        rw [this]; exact hik
      rw [hidx] at hb
      rw [hb]
      exact le_max_right _ _
