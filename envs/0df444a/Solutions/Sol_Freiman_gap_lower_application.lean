-- Prove2me | solution 1 for Freiman.gap_lower_application
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:22:33.515162+00:00
-- url     : https://prove2.me/submissions/3bb2697e-4bdc-422d-8d8e-1f6db4442397

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



private theorem recentered_match (a : ℤ → ℕ+) (i : ℤ) (s : GapState)
    (hs : s.centre < s.word.length) (hm : gapMatch a i ⟨s.word, 0⟩) :
    gapMatch a (i + (s.centre : ℤ)) s := by
  refine ⟨hs, ?_⟩
  intro n hn
  have hh := hm.2 n hn
  change a (i + (n : ℤ) - 0) = s.word[n]! at hh
  have hi : (i + (s.centre : ℤ)) + (n : ℤ) - (s.centre : ℤ) = i + (n : ℤ) - 0 := by omega
  rw [hi]
  exact hh



theorem solution (hsound : GapCertificateSoundness) (hb : gapLowerRows.length = 19 ∧ gapLowerTrees.length = 19 ∧ ∀ n : ℕ, n < 19 → gapRoot (gapLowerTrees[n]!) = (gapLowerRows[n]!).state) (hcoverage : ∀ tree ∈ gapLowerTrees, gapCoverage tree) (hchecks : ∀ n : ℕ, n < 19 → gapChecks (gapLowerRows.take n) [] .forbidden (gapLowerTrees[n]!)) (a : ℤ → ℕ+) (hd : gapDigits a) (hc : gapCapped a) : gapLowerValid a gapLowerRows := by
  have hall : ∀ n : ℕ, n < 19 → ∀ b : ℤ → ℕ+,
      gapDigits b → gapCapped b → gapAvoids b (gapLowerRows[n]!).state.word := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn b hdb hcb
      have hnt : n < gapLowerTrees.length := by omega
      have htmem : gapLowerTrees[n]! ∈ gapLowerTrees := by
        rw [getElem!_pos gapLowerTrees n hnt]
        exact List.getElem_mem hnt
      have hcov := hcoverage _ htmem
      have hbroot := hb.2.2 n hn
      have hs : (gapLowerRows[n]!).state.centre < (gapLowerRows[n]!).state.word.length := by
        rw [← hbroot]
        exact coverage_root _ hcov
      have hprior (c : ℤ → ℕ+) (hdc : gapDigits c) (hcc : gapCapped c) :
          gapLowerValid c (gapLowerRows.take n) := by
        intro row hr
        obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hr
        have hkn : k < n := by
          have hlen := List.length_take_le n gapLowerRows
          omega
        have hkl : k < gapLowerRows.length := by omega
        have heq : gapLowerRows[k]! = row := by
          rw [getElem!_pos gapLowerRows k hkl]
          simpa only [List.getElem_take] using hkeq
        rw [← heq]
        exact ih k hkn (lt_trans hkn hn) c hdc hcc
      have hnone (c : ℤ → ℕ+) : gapUpperValid c [] := by intro row hr; simp at hr
      have hforbid (c : ℤ → ℕ+) (hdc : gapDigits c) (hcc : gapCapped c) (j : ℤ)
          (hm : gapMatch c j (gapLowerRows[n]!).state) : False := by
        apply hsound (gapLowerRows.take n) [] .forbidden (gapLowerTrees[n]!) c j
          hdc hcc (hprior c hdc hcc) (hnone c) hcov (hchecks n hn)
        rw [hbroot]
        exact hm
      constructor
      · intro j hm
        exact hforbid b hdb hcb _ (recentered_match b j _ hs hm)
      · intro j hm
        have hsr : (gapReverse (gapLowerRows[n]!).state).centre <
            (gapReverse (gapLowerRows[n]!).state).word.length := by
          simp only [gapReverse, List.length_reverse]
          omega
        have hmr := recentered_match b j (gapReverse (gapLowerRows[n]!).state) hsr hm
        have hmb := reflected_match b _ (gapLowerRows[n]!).state hs hmr
        exact hforbid (gapReflect b) (fun i => hdb (-i)) (gap_reflect_capped b hcb) _ hmb
  intro row hr
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hr
  have hn19 : n < 19 := by omega
  rw [← getElem!_pos gapLowerRows n hn]
  exact hall n hn19 a hd hc

