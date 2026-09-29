-- Prove2me | solution 1 for Freiman.gap_leaf_prior_soundness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:25:34.312852+00:00
-- url     : https://prove2.me/submissions/9e7c0d29-41c1-46b2-a854-8db7e9d441ce

import Definitions.Def_Freiman_gapCertificateData

open Freiman

private theorem contained_match (a : ℤ → ℕ+) (i : ℤ) (s : GapState)
    (w : List ℕ+) (hm : gapMatch a i s) (hw : w ≠ [])
    (hc : gapWordContains s w) : ∃ j, gapMatch a j ⟨w, 0⟩ := by
  obtain ⟨k, hword⟩ := hc
  refine ⟨i + (k : ℤ) - (s.centre : ℤ), ?_⟩
  refine ⟨List.length_pos_iff.mpr hw, ?_⟩
  intro n hn
  change n < w.length at hn
  have hlen := congrArg List.length hword
  simp only [List.length_take, List.length_drop] at hlen
  have hkn : k + n < s.word.length := by omega
  have hi : (i + (k : ℤ) - (s.centre : ℤ)) + (n : ℤ) - (0 : ℤ) =
      i + ((k + n : ℕ) : ℤ) - (s.centre : ℤ) := by omega
  change a ((i + (k : ℤ) - (s.centre : ℤ)) + (n : ℤ) - (0 : ℤ)) = w[n]!
  rw [hi, hm.2 (k + n) hkn]
  have hh := congrArg (fun v : List ℕ+ => v[n]!) hword
  simpa [List.getElem!_eq_getElem?_getD, List.getElem?_take, hn,
    List.getElem?_drop] using hh



theorem solution (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s) (n : ℕ) (hcheck : gapLeafCheck lower upper mode s (.prior n)) : gapModeOutcome mode a i := by
  rcases hcheck with ⟨hn, hw, ht⟩
  have hrowmem : lower[n]! ∈ lower := by
    rw [getElem!_pos lower n hn]
    exact List.getElem_mem hn
  have hav := hl _ hrowmem
  exfalso
  rcases ht with ht | ht
  · obtain ⟨j, hj⟩ := contained_match a i s _ hm hw ht
    exact hav.1 j hj
  · have hr : (lower[n]!).state.word.reverse ≠ [] := by simpa using hw
    obtain ⟨j, hj⟩ := contained_match a i s _ hm hr ht
    exact hav.2 j hj

