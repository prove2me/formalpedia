-- Prove2me | solution 1 for Freiman.gap_upper_application
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:22:59.765706+00:00
-- url     : https://prove2.me/submissions/b58a6e03-e385-47cd-9d6d-69c22a7303b5

import Theorems.Thm_Freiman_gap_reflection
import Theorems.Thm_Freiman_gap_reflect_capped
import Definitions.Def_Freiman_gapCertificateData

open Freiman

private theorem coverage_root (t : GapTree) (h : gapCoverage t) :
    (gapRoot t).centre < (gapRoot t).word.length := by
  cases t with
  | leaf s reason => exact h
  | split s side one two three four => exact h.1

private theorem reflected_match (a : ℤ → ℕ+) (i : ℤ) (s : GapState)
    (hs : s.centre < s.word.length) (hm : gapMatch a i (gapReverse s)) :
    gapMatch (gapReflect a) (-i) s := by
  refine ⟨hs, ?_⟩
  intro n hn
  have hnr : s.word.length - 1 - n < (gapReverse s).word.length := by
    simp only [gapReverse, List.length_reverse]
    omega
  have hkey := hm.2 (s.word.length - 1 - n) hnr
  have hrev : (gapReverse s).word[s.word.length - 1 - n]! = s.word[n]! := by
    change s.word.reverse[s.word.length - 1 - n]! = s.word[n]!
    have hnr2 : s.word.length - 1 - n < s.word.reverse.length := by simpa [gapReverse] using hnr
    rw [getElem!_pos s.word.reverse (s.word.length - 1 - n) hnr2,
      getElem!_pos s.word n hn, List.getElem_reverse]
    congr 1
    omega
  rw [hrev] at hkey
  have hi : i + ((s.word.length - 1 - n : ℕ) : ℤ) -
      ((gapReverse s).centre : ℤ) = -((-i) + (n : ℤ) - (s.centre : ℤ)) := by
    change i + ((s.word.length - 1 - n : ℕ) : ℤ) -
      ((s.word.length - 1 - s.centre : ℕ) : ℤ) = _
    omega
  rw [hi] at hkey
  exact hkey



theorem solution (hsound : GapCertificateSoundness) (hb : gapUpperRows.length = 11 ∧ gapUpperTrees.length = 11 ∧ ∀ n : ℕ, n < 11 → gapRoot (gapUpperTrees[n]!) = (gapUpperRows[n]!).state) (hcoverage : ∀ tree ∈ gapUpperTrees, gapCoverage tree) (hchecks : ∀ n : ℕ, n < 11 → gapChecks [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!)) (a : ℤ → ℕ+) (hd : gapDigits a) (hc : gapCapped a) : gapUpperValid a gapUpperRows := by
  intro row hrow i hm
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hrow
  have hn11 : n < 11 := by omega
  have hnt : n < gapUpperTrees.length := by omega
  have htmem : gapUpperTrees[n]! ∈ gapUpperTrees := by
    rw [getElem!_pos gapUpperTrees n hnt]
    exact List.getElem_mem hnt
  have hcov := hcoverage _ htmem
  have hbroot := hb.2.2 n hn11
  have hs : (gapUpperRows[n]!).state.centre < (gapUpperRows[n]!).state.word.length := by
    rw [← hbroot]
    exact coverage_root _ hcov
  have hnoneL (b : ℤ → ℕ+) : gapLowerValid b [] := by intro row hr; simp at hr
  have hnoneU (b : ℤ → ℕ+) : gapUpperValid b [] := by intro row hr; simp at hr
  rw [← getElem!_pos gapUpperRows n hn] at hm ⊢
  rcases hm with hm | hm
  · apply hsound [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!) a i
        hd hc (hnoneL a) (hnoneU a) hcov (hchecks n hn11)
    rw [hbroot]
    exact hm
  · have hmatch := reflected_match a i _ hs hm
    have hd' : gapDigits (gapReflect a) := fun j => hd (-j)
    have hv := hsound [] [] (.upper (gapUpperRows[n]!).bound) (gapUpperTrees[n]!)
      (gapReflect a) (-i) hd' (gap_reflect_capped a hc)
      (hnoneL _) (hnoneU _) hcov (hchecks n hn11) (by rw [hbroot]; exact hmatch)
    change localValue (gapReflect a) (-i) < ((gapUpperRows[n]!).bound : ℝ) at hv
    simpa only [gap_reflection, neg_neg] using hv

