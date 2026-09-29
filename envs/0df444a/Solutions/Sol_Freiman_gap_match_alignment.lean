-- Prove2me | solution 1 for Freiman.gap_match_alignment
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:42:30.883448+00:00
-- url     : https://prove2.me/submissions/f95ec277-e32d-42bc-a5ca-b5fc743bb1b3

import Definitions.Def_Freiman_gapCertificateData

set_option autoImplicit false
open Freiman

theorem solution (a : ℤ → ℕ+) (i : ℤ) (s v : GapState)
    (hm : gapMatch a i s) (hv : v.centre < v.word.length)
    (hc : gapAlignedContains s v) : gapMatch a i v := by
  obtain ⟨k, hw, hcentre⟩ := hc
  refine ⟨hv, ?_⟩
  intro n hn
  have hlen := congrArg List.length hw
  simp only [List.length_take, List.length_drop] at hlen
  have hkn : k + n < s.word.length := by omega
  have hi : i + (n : ℤ) - (v.centre : ℤ) =
      i + ((k + n : ℕ) : ℤ) - (s.centre : ℤ) := by
    rw [hcentre]
    push_cast
    omega
  rw [hi, hm.2 (k + n) hkn]
  have hh := congrArg (fun w : List ℕ+ => w[n]!) hw
  simpa [List.getElem!_eq_getElem?_getD, List.getElem?_take, hn,
    List.getElem?_drop] using hh
