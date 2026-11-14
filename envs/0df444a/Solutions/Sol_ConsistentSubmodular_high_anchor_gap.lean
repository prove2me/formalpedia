-- Prove2me | solution 1 for ConsistentSubmodular.high_anchor_gap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:30.080221+00:00
-- url     : https://prove2.me/submissions/fb6ebeda-2864-4edb-ae71-f0e4ed202c9a

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
import Theorems.Thm_ConsistentSubmodular_high_anchor_low_baseline_error

section

open ConsistentSubmodular

theorem solution (d p δ w b q : ℝ)
    (hd : 0 < d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hb : p + d ≤ b) (hq1 : 1 ≤ q) (hq3 : q < 3)
    (hatt : q * (δ + w) = 3 * w - b - 3 * d)
    (hfail : 3 * (1 - 4 * d) < (2 * (1 - d) - b - w) * q) :
    3 * d < w := by
  let A := 1 - d
  let D := 3 * d
  let L := p + d
  let B := 1 - 4 * d
  let F := fun b w : ℝ => (2 * A - b - w) * (3 * w - b - D)
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := by dsimp [B]; linarith
  have hq : 0 < q := by linarith
  have hL : 2 * d ≤ L := by
    dsimp [L]
    rcases hcredit with h | h
    · linarith
    · nlinarith [sq_nonneg p]
  have hLB : L ≤ b := hb
  have hb0 : 0 ≤ b := by dsimp [L] at hLB; linarith
  have hw : 0 < w := by
    have hqδ := mul_nonneg hq.le hδ
    have hscaled : 0 < (3 - q) * w := by nlinarith only [hatt, hqδ, hb0, hd]
    exact (mul_pos_iff_of_pos_left (sub_pos.mpr hq3)).mp hscaled
  have hpos : 0 < 2 * A - b - w := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hq.le
    dsimp [A] at *
    linarith
  have hbound : b + D ≤ 2 * w := by
    have h1 := mul_nonneg (sub_nonneg.mpr hq1) hw.le
    have h2 := mul_nonneg hq.le hδ
    dsimp [D]
    nlinarith
  have hfailed : 3 * B * w < F b w := by
    have h1 := mul_lt_mul_of_pos_right hfail hw
    have h2 := mul_nonneg (mul_nonneg hpos.le hq.le) hδ
    have heq := congrArg (fun x : ℝ => (2 * A - b - w) * x) hatt
    dsimp [A, B, D, F] at *
    nlinarith only [h1, h2, heq]
  by_contra hn
  have hwD : w ≤ D := le_of_not_gt hn
  have hbD : b ≤ D := by linarith
  have hLD : L ≤ D := hLB.trans hbD
  have hstrong : d ≤ p * (1 - p) := by
    rcases hcredit with h | h
    · dsimp [L, D] at hLD
      linarith
    · exact h
  have he := high_anchor_low_baseline_error d p hd.le hd7 hp
    (by dsimp [L, D] at hLD; linarith) hstrong
  have hcompare : F b w ≤ F L w := by
    have hfactor : 0 ≤ 2 * w + 2 * A - D - b - L := by
      dsimp [A, D] at *
      linarith
    have := mul_nonneg (sub_nonneg.mpr hLB) hfactor
    dsimp [F]
    nlinarith only [this]
  have hinner : 0 ≤ (2 * A - L) * (L + D) - 3 * D * w := by
    have h1 := mul_nonneg hd.le (show 0 ≤ 10 - 47 * d by linarith)
    have h2 := mul_nonneg (sub_nonneg.mpr hL)
      (show 0 ≤ 2 - 7 * d - L by dsimp [L, D] at hLD; dsimp [L]; linarith)
    have h3 := mul_nonneg (show 0 ≤ 3 * D by positivity) (sub_nonneg.mpr hwD)
    dsimp [A, D] at *
    nlinarith only [h1, h2, h3]
  have hmon : D * F L w ≤ w * F L D := by
    have := mul_nonneg (sub_nonneg.mpr hwD) hinner
    dsimp [F]
    nlinarith only [this]
  have hendpoint : F L D ≤ 3 * B * D := by
    dsimp [F, A, D, L, B]
    unfold relayError at he
    nlinarith only [he]
  have hbad : 3 * B * D * w < 3 * B * D * w := by
    calc
      3 * B * D * w = D * (3 * B * w) := by ring
      _ < D * F b w := mul_lt_mul_of_pos_left hfailed hD
      _ ≤ D * F L w := mul_le_mul_of_nonneg_left hcompare hD.le
      _ ≤ w * F L D := hmon
      _ ≤ w * (3 * B * D) := mul_le_mul_of_nonneg_left hendpoint hw.le
      _ = _ := by ring
  exact (lt_irrefl _) hbad

end
