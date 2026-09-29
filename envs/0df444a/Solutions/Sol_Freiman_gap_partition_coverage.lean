-- Prove2me | solution 1 for Freiman.gap_partition_coverage
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:23:22.870063+00:00
-- url     : https://prove2.me/submissions/803e568f-119c-4bd1-8756-eabe87964301

import Definitions.Def_Freiman_gapCertificateData

set_option maxHeartbeats 800000

open Freiman

private theorem extend_match (a : ℤ → ℕ+) (i : ℤ) (s : GapState)
    (hm : gapMatch a i s) (left : Bool) :
    gapMatch a i (gapExtend s left
      (a (if left then i - (s.centre : ℤ) - 1 else i + (s.word.length : ℤ) - (s.centre : ℤ)))) := by
  cases left with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, gapExtend]
    refine ⟨by simpa using Nat.lt_succ_of_lt hm.1, ?_⟩
    intro n hn
    simp only [List.length_append, List.length_singleton] at hn
    by_cases hnl : n < s.word.length
    · simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hnl] using hm.2 n hnl
    · have heq : n = s.word.length := by simpa using (by omega : n = s.word.length)
      subst n
      simp
  | true =>
    simp only [gapExtend, ↓reduceIte]
    refine ⟨by simpa using hm.1, ?_⟩
    intro n hn
    cases n with
    | zero =>
      simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one, List.getElem!_cons_zero]
      congr 1
      omega
    | succ n =>
      have hnl : n < s.word.length := by simpa using hn
      have heq : i + ((n + 1 : ℕ) : ℤ) - ((s.centre + 1 : ℕ) : ℤ) =
          i + (n : ℤ) - (s.centre : ℤ) := by omega
      change a (i + ((n + 1 : ℕ) : ℤ) - ((s.centre + 1 : ℕ) : ℤ)) = s.word[n]!
      rw [heq]
      exact hm.2 n hnl


theorem solution (tree : GapTree) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCoverage tree) (hm : gapMatch a i (gapRoot tree)) : ∃ s r, (s,r) ∈ gapLeaves tree ∧ gapMatch a i s := by
  induction tree with
  | leaf s r => exact ⟨s, r, by simp [gapLeaves], hm⟩
  | split s left one two three four ih1 ih2 ih3 ih4 =>
    rcases hc with ⟨hs, hr1, hr2, hr3, hr4, hc1, hc2, hc3, hc4⟩
    let d := a (if left then i - (s.centre : ℤ) - 1 else
      i + (s.word.length : ℤ) - (s.centre : ℤ))
    have hdm : gapMatch a i (gapExtend s left d) := extend_match a i s hm left
    have hpos : 0 < (d : ℕ) := d.pos
    have hle : (d : ℕ) ≤ 4 := hd _
    have hdv : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by
      have hdv : (d : ℕ) = 1 ∨ (d : ℕ) = 2 ∨ (d : ℕ) = 3 ∨ (d : ℕ) = 4 := by omega
      simpa only [← PNat.coe_inj, PNat.val_ofNat] using hdv
    rcases hdv with hdv | hdv | hdv | hdv
    · rw [hdv] at hdm
      obtain ⟨v, r, hmem, hmatch⟩ := ih1 hc1 (by rw [hr1]; exact hdm)
      exact ⟨v, r, by simp [gapLeaves, hmem], hmatch⟩
    · rw [hdv] at hdm
      obtain ⟨v, r, hmem, hmatch⟩ := ih2 hc2 (by rw [hr2]; exact hdm)
      exact ⟨v, r, by simp [gapLeaves, hmem], hmatch⟩
    · rw [hdv] at hdm
      obtain ⟨v, r, hmem, hmatch⟩ := ih3 hc3 (by rw [hr3]; exact hdm)
      exact ⟨v, r, by simp [gapLeaves, hmem], hmatch⟩
    · rw [hdv] at hdm
      obtain ⟨v, r, hmem, hmatch⟩ := ih4 hc4 (by rw [hr4]; exact hdm)
      exact ⟨v, r, by simp [gapLeaves, hmem], hmatch⟩

