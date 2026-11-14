-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.after_credit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:05.994602+00:00
-- url     : https://prove2.me/submissions/4ae913ac-a73b-474d-9eb0-c6364a4e9224

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackAfter
import Theorems.Thm_ConsistentSubmodular_LowRollback_remainder_positive

section

set_option maxHeartbeats 2000000

namespace ConsistentSubmodular.LowRollback

private theorem nzero_negative (k q : ℝ) (hk : k ≤ 40 / 17)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hH : 20 - 11 * k + (2 * k - 5) * q < 0) : nzero k q < 0 := by
  let v := (20 - 5 * q) / (11 - 2 * q)
  have hden : 0 < 11 - 2 * q := by linarith
  have hvk : v < k := by apply (div_lt_iff₀ hden).mpr; nlinarith
  have hA : 0 ≤ q ^ 2 - 8 * q + 20 := by nlinarith [sq_nonneg (q - 4)]
  have hbracket : (q ^ 2 - 8 * q + 20) * (k + v) + (-7 * q ^ 2 + 53 * q - 116) < 0 := by
    have hh := mul_nonneg hA (show 0 ≤ 80 / 17 - (k + v) by linarith)
    have hc : 0 < 13 * q ^ 2 - 87 * q + 124 := by nlinarith [sq_nonneg q]
    nlinarith
  have hmon : nzero k q < nzero v q := by
    have heq : nzero k q - nzero v q =
        (k - v) * ((q ^ 2 - 8 * q + 20) * (k + v) + (-7 * q ^ 2 + 53 * q - 116)) := by unfold nzero; ring
    have hm := mul_neg_of_pos_of_neg (sub_pos.mpr hvk) hbracket
    linarith
  have hv : nzero v q < 0 := by
    have heq : (11 - 2 * q) ^ 2 * nzero v q =
        -(q - 4) * (5 * q ^ 3 - 31 * q ^ 2 - 19 * q - 24) := by
      dsimp [nzero, v]
      field_simp
      ring
    have hc : 5 * q ^ 3 - 31 * q ^ 2 - 19 * q - 24 < 0 := by
      have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 5 * q ^ 2 by positivity)
        (show q - 1 ≤ 0 by linarith)
      nlinarith [sq_nonneg q]
    have hn : 0 < -(q - 4) := by linarith
    have hm := mul_neg_of_pos_of_neg hn hc
    rw [← heq] at hm
    nlinarith only [hm, sq_pos_of_pos hden]
  exact hmon.trans hv

end ConsistentSubmodular.LowRollback

end

section

set_option maxHeartbeats 2000000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (k q d₀ d p δ P : ℝ)
    (hk0 : 40 / 23 < k) (hk1 : k < 40 / 17) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hH : 20 - 11 * k + (2 * k - 5) * q < 0) (hd₀ : 0 ≤ d₀) (hδ : 0 ≤ δ)
    (hF : 0 ≤ parentFloor k d₀ d p)
    (hT : 0 ≤ childPersistence q d p δ P)
    (hC : 0 ≤ childCapacity q d δ P)
    (hE : 0 ≤ childIneligibility q d P) : 0 < Y k d₀ d p δ P := by
  let x := k - 2
  let L := (k - 1) * (3 - k)
  let D := 3 * q ^ 2 - 21 * q + 36 - k * (q ^ 2 - 6 * q + 12)
  let S := 4 * (4 - q) * D
  let R := (3 - k) * cpoly q - k * apoly q
  let Aq := (x - 1) ^ 2 * (x + 1)
  let Bq := -x ^ 4 - 7 * x ^ 3 + 13 * x ^ 2 + 11 * x - 7
  let Cq := 4 * x ^ 4 + 16 * x ^ 3 - 24 * x ^ 2 - 16 * x + 20
  let N₁ := Aq * q ^ 2 + Bq * q + Cq
  let N₃ := q * Aq - 3 * x ^ 3 + 6 * x ^ 2 - 12
  let N₀ := nzero k q
  let R₀ := (3 - q) ^ 2 * x ^ 2 * (2 - x) + q ^ 2 * (1 + x)
  let G := q * N₁ - (4 - q) * D * L * (k - 1)
  let AF := 4 * k * (4 - q) ^ 2 * (4 - q - x ^ 2)
  let AT := 4 * N₁
  let AE := -k * (4 - q) * N₃
  let Ad := -4 * k * (4 - k) * (4 - q) * N₀
  let A₀ := 4 * k * (4 - q) * R₀
  have hk : 0 < k := by linarith
  have hk3 : 0 < 3 - k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hq3 : 0 < 3 - q := by linarith
  have hq4 : 0 < 4 - q := by linarith
  have h1q : 0 ≤ 1 - q := by linarith
  have hxlo : -(3 / 8) ≤ x := by dsimp [x]; linarith
  have hxhi : x ≤ 3 / 8 := by dsimp [x]; linarith
  have hxhalf0 : -(1 / 2) ≤ x := by linarith
  have hxhalf1 : x ≤ 1 / 2 := by linarith
  have hxplus : 0 < x + 1 := by linarith
  have hxminus : 0 < 2 - x := by linarith
  have hx2 : x ^ 2 ≤ 9 / 64 := by nlinarith
  have hx2half : x ^ 2 ≤ 1 / 4 := by linarith
  have hx3lo : -(27 / 512) ≤ x ^ 3 := by
    have hm := mul_nonneg (sq_nonneg x) (show 0 ≤ x + 3 / 8 by linarith)
    nlinarith
  have hx3half : -(1 / 8) ≤ x ^ 3 := by linarith
  have hc : 14 ≤ cpoly q := by
    have heq : cpoly q = 14 + 25 * (1 - q) + 8 * (1 - q) ^ 2 + (1 - q) ^ 3 := by unfold cpoly; ring
    rw [heq]
    have hp := pow_nonneg h1q 3
    nlinarith [sq_nonneg (1 - q)]
  have ha : apoly q ≤ 3 := by
    have hm := mul_nonneg h1q hq3.le
    unfold apoly
    nlinarith
  have hR : 0 < R := by
    have h1 := mul_le_mul_of_nonneg_left hc hk3.le
    have h2 := mul_le_mul_of_nonneg_left ha hk.le
    dsimp [R]
    nlinarith
  have hD : 0 < D := by
    have hm := mul_nonneg h1q
      (show 0 ≤ (3 - k) * (1 - q) + (15 - 4 * k) by
        have hm := mul_nonneg hk3.le h1q
        linarith)
    have heq : D - (18 - 7 * k) = (1 - q) * ((3 - k) * (1 - q) + (15 - 4 * k)) := by dsimp [D]; ring
    linarith
  have hS : 0 < S := by dsimp [S]; positivity
  have hAq : 0 ≤ Aq := by dsimp [Aq]; positivity
  have hBq : Bq < 0 := by
    dsimp [Bq]
    nlinarith only [hx2, hx3lo, hxhi, pow_nonneg (sq_nonneg x) 2]
  have hN₁ : 0 < N₁ := by
    have h1 := mul_nonneg hAq (sq_nonneg q)
    have h2 := mul_nonneg (neg_nonneg.mpr hBq.le) h1q
    have h3 : 0 < Bq + Cq := by
      dsimp [Bq, Cq]
      nlinarith only [hx2half, hx3half, hxhalf1, pow_nonneg (sq_nonneg x) 2]
    dsimp [N₁]
    linarith
  have hN₃ : N₃ < 0 := by
    have h1 := mul_nonneg h1q hAq
    have h2 : Aq - 3 * x ^ 3 + 6 * x ^ 2 - 12 < 0 := by
      dsimp [Aq]
      nlinarith only [hx2half, hx3half, hxhalf0]
    dsimp [N₃]
    linarith
  have hN₀ : N₀ < 0 := nzero_negative k q hk1.le hq0.le hq1 hH
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hxminus.le)
      (mul_pos (sq_pos_of_pos hq0) (by linarith))
  have hAF : 0 ≤ AF := by
    dsimp [AF]
    have hlast : 0 ≤ 4 - q - x ^ 2 := by linarith
    positivity
  have hAT : 0 ≤ AT := by dsimp [AT]; positivity
  have hAE : 0 ≤ AE := by
    change 0 ≤ -k * (4 - q) * N₃
    exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith) hN₃.le
  have hAd : 0 ≤ Ad := by
    have heq : Ad = 4 * k * (4 - k) * (4 - q) * (-N₀) := by dsimp [Ad]; ring
    rw [heq]
    exact mul_nonneg (by positivity) (neg_nonneg.mpr hN₀.le)
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  have hid1 : S * k * Y k d₀ d p δ P =
      AF * parentFloor k d₀ d p + AT * childPersistence q d p δ P - G * childCapacity q d δ P+
      AE * childIneligibility q d P + Ad * d₀ + A₀ := by
    dsimp [S, D, Y, ceiling, AF, AT, N₁, Aq, Bq, Cq, G, L, AE, N₃, Ad, N₀, nzero, A₀, R₀,
      parentFloor, childPersistence, childCapacity, childIneligibility, x]
    field_simp
    ring
  by_cases hG : G ≤ 0
  · have h1 := mul_nonneg hAF hF
    have h2 := mul_nonneg hAT hT
    have h3 := mul_nonpos_of_nonpos_of_nonneg hG hC
    have h4 := mul_nonneg hAE hE
    have h5 := mul_nonneg hAd hd₀
    have hy : 0 < S * k * Y k d₀ d p δ P := by rw [hid1]; linarith only [h1, h2, h3, h4, h5, hA₀]
    exact (mul_pos_iff_of_pos_left (mul_pos hS hk)).mp hy
  · have hGpos : 0 ≤ G := le_of_not_ge hG
    let hFcoef := 16 * (4 - q)
    let hTcoef := 16 * (3 - k)
    let hEcoef := (4 - q) * (k * q - 6 * k - 3 * q + 21)
    let hdcoef := 32 * (4 - k) * (4 - q)
    have hhF : 0 ≤ hFcoef := by dsimp [hFcoef]; positivity
    have hhT : 0 ≤ hTcoef := by dsimp [hTcoef]; positivity
    have hhE : 0 ≤ hEcoef := by
      dsimp [hEcoef]
      apply mul_nonneg hq4.le
      have hm := mul_nonneg hk3.le h1q
      nlinarith
    have hhd : 0 ≤ hdcoef := by dsimp [hdcoef]; positivity
    have hrem := remainder_positive x q hxhalf0 hxhalf1 hq0.le hq1
    have hid2 : S * R * k * Y k d₀ d p δ P =
        (R * AF + G * hFcoef) * parentFloor k d₀ d p+
        (R * AT + G * hTcoef) * childPersistence q d p δ P + S * G * δ+
        (R * AE + G * hEcoef) * childIneligibility q d P+
        (R * Ad + G * hdcoef) * d₀ + S * remainder x q := by
      dsimp [S, R, D, Y, ceiling, AF, AT, N₁, Aq, Bq, Cq, G, L, AE, N₃, Ad, N₀, nzero,
        hFcoef, hTcoef, hEcoef, hdcoef, remainder, parentFloor, childPersistence,
        childIneligibility, cpoly, apoly, x]
      field_simp
      ring
    have h1 := mul_nonneg (add_nonneg (mul_nonneg hR.le hAF) (mul_nonneg hGpos hhF)) hF
    have h2 := mul_nonneg (add_nonneg (mul_nonneg hR.le hAT) (mul_nonneg hGpos hhT)) hT
    have h3 := mul_nonneg (mul_nonneg hS.le hGpos) hδ
    have h4 := mul_nonneg (add_nonneg (mul_nonneg hR.le hAE) (mul_nonneg hGpos hhE)) hE
    have h5 := mul_nonneg (add_nonneg (mul_nonneg hR.le hAd) (mul_nonneg hGpos hhd)) hd₀
    have h6 := mul_pos hS hrem
    have hy : 0 < S * R * k * Y k d₀ d p δ P := by rw [hid2]; linarith only [h1, h2, h3, h4, h5, h6]
    exact (mul_pos_iff_of_pos_left (mul_pos (mul_pos hS hR) hk)).mp hy

end
