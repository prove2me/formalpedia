-- Prove2me | solution 1 for Freiman.gap_leaf_upperRow_soundness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:26:35.99899+00:00
-- url     : https://prove2.me/submissions/17ee86ae-ef5e-4ce7-b2fd-92907a613c2d

import Definitions.Def_Freiman_gapCertificateData

open Freiman

private theorem aligned_match (a : ℤ → ℕ+) (i : ℤ) (s v : GapState)
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


theorem solution (lower upper : List GapRow) (mode : GapMode) (s : GapState) (a : ℤ → ℕ+) (i : ℤ) (hd : gapDigits a) (hc : gapCapped a) (hl : gapLowerValid a lower) (hu : gapUpperValid a upper) (hm : gapMatch a i s) (n : ℕ) (hcheck : gapLeafCheck lower upper mode s (.upperRow n)) : gapModeOutcome mode a i := by
  rcases hcheck with ⟨hn, hv, hb, hcontains⟩
  have hrowmem : upper[n]! ∈ upper := by
    rw [getElem!_pos upper n hn]
    exact List.getElem_mem hn
  have hmatch : gapMatch a i (upper[n]!).state ∨
      gapMatch a i (gapReverse (upper[n]!).state) := by
    rcases hcontains with ht | ht
    · exact Or.inl (aligned_match a i s _ hm hv ht)
    · apply Or.inr
      apply aligned_match a i s _ hm _ ht
      simp only [gapReverse, List.length_reverse]
      omega
  have hlt := hu _ hrowmem i hmatch
  cases mode with
  | forbidden => exact hb.elim
  | upper cut =>
    change localValue a i < (cut : ℝ)
    have hle : ((upper[n]!).bound : ℝ) ≤ (cut : ℝ) := by exact_mod_cast hb
    exact hlt.trans_le hle
  | reduction =>
    intro hw
    have hle : ((upper[n]!).bound : ℝ) ≤ gapWindow := by
      change (upper[n]!).bound ≤ 2263914769 / 500000000 at hb
      simpa only [Rat.cast_div, Rat.cast_ofNat, gapWindow] using (Rat.cast_le (K := ℝ)).2 hb
    exact False.elim (not_lt_of_ge (hlt.trans_le hle).le hw)

