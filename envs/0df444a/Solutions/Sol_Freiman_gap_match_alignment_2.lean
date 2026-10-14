-- Prove2me | solution 2 for Freiman.gap_match_alignment
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-10T14:49:04.854681+00:00
-- url     : https://prove2.me/submissions/8e78fc4f-1779-42b5-a3ce-0035934a4fa0

import Definitions.Def_Freiman_gapCertificateData

open Freiman

theorem solution (a : ℤ → ℕ+) (i : ℤ) (s v : GapState) (hm : gapMatch a i s)
    (hv : v.centre < v.word.length) (hc : gapAlignedContains s v) : gapMatch a i v := by
  obtain ⟨k, hk, hcentre⟩ := hc
  refine ⟨hv, ?_⟩
  intro n hn
  -- the copy of `v.word` sitting at offset `k` fits inside `s.word`
  have hlen : k + v.word.length ≤ s.word.length := by
    have h := congrArg List.length hk
    simp only [List.length_take, List.length_drop] at h
    omega
  have hkn : k + n < s.word.length := by omega
  -- corresponding entries agree
  have hval : v.word[n]! = s.word[k + n]! := by
    rw [← hk]
    rw [getElem!_pos ((s.word.drop k).take v.word.length) n
        (by simp only [List.length_take, List.length_drop]; omega),
      getElem!_pos s.word (k + n) hkn]
    simp [List.getElem_take, List.getElem_drop]
  have hs := hm.2 (k + n) hkn
  rw [hval, ← hs]
  congr 1
  rw [hcentre]
  push_cast
  ring
