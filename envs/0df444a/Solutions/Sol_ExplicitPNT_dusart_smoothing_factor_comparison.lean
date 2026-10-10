-- Prove2me | solution 1 for ExplicitPNT.dusart_smoothing_factor_comparison
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T15:50:37.094088+00:00
-- url     : https://prove2.me/submissions/7928bdb0-ae56-427b-8e63-540db6112323

import Mathlib

set_option maxHeartbeats 800000

namespace DusartComparison

lemma exponential_loss (X L : ℝ) (hX : 8 ≤ X) (hL : 3 / 2 ≤ L) :
    (591 / 25 : ℝ) * Real.sqrt X * Real.exp (-X) < L / X := by
  have hXp : 0 < X := by linarith
  have hs := Real.sqrt_nonneg X
  have hs2 := Real.sq_sqrt hXp.le
  have hsmin : (14 / 5 : ℝ) ≤ Real.sqrt X := by nlinarith
  have hX4 : (4096 : ℝ) ≤ X ^ 4 := by
    have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hX 4
    norm_num at ht
    exact ht
  have hlarge : 480 * (591 / 25 : ℝ) < X ^ 4 * Real.sqrt X := by
    calc
      480 * (591 / 25 : ℝ) < 4096 * (14 / 5 : ℝ) := by norm_num
      _ ≤ X ^ 4 * Real.sqrt X := by gcongr
  have hmul := mul_lt_mul_of_pos_right hlarge
    (mul_pos hXp (Real.sqrt_pos.2 hXp))
  have hid : (X ^ 4 * Real.sqrt X) * (X * Real.sqrt X) = X ^ 6 := by
    calc
      _ = X ^ 5 * (Real.sqrt X) ^ 2 := by ring
      _ = X ^ 6 := by rw [hs2]; ring
  rw [hid] at hmul
  have ht : X ^ 6 / (720 : ℝ) ≤ Real.exp X := by
    simpa [Nat.factorial] using Real.pow_div_factorial_le_exp X hXp.le 6
  have hpoly : (591 / 25 : ℝ) * (X * Real.sqrt X) <
      (3 / 2 : ℝ) * (X ^ 6 / 720) := by nlinarith
  have hfinal : (591 / 25 : ℝ) * (X * Real.sqrt X) < L * Real.exp X := by
    calc
      _ < (3 / 2 : ℝ) * (X ^ 6 / 720) := hpoly
      _ ≤ (3 / 2 : ℝ) * Real.exp X := by gcongr
      _ ≤ L * Real.exp X := by gcongr
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_div_iff₀ (Real.exp_pos X) hXp).2
  nlinarith [hfinal]

end DusartComparison

theorem solution (X ν L : ℝ)
    (hX : 8 ≤ X) (hν : 97 / 100 ≤ ν) (hν1 : ν < 1)
    (hL : 3 / 2 ≤ L) (hL7 : L ≤ 7) :
    Real.sqrt (Real.sqrt
      (ν ^ 6 / (2 * ν ^ 2 - 1) *
        (1 - (L - 1 / 2) / (X * ν)) * (1 - L / (X * ν)))) *
      Real.exp ((591 / 100 : ℝ) * Real.sqrt X * Real.exp (-X)) <
        Real.sqrt (Real.sqrt (1 - (L - 1 / 2) / X)) := by
  have hXp : 0 < X := by linarith
  have hνp : 0 < ν := by linarith
  have hν9 : (9 / 10 : ℝ) ≤ ν := by linarith
  have hν2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) hν9 2
  have hD : 0 < 2 * ν ^ 2 - 1 := by norm_num at hν2; linarith
  have hLX : L / X < ν := by
    apply (div_lt_iff₀ hXp).2
    have hm : (97 / 100 : ℝ) * 8 ≤ ν * X := by gcongr
    linarith
  let q : ℝ := (L - 1 / 2) / X
  let B : ℝ := 1 - q
  let F : ℝ := ν ^ 4 * (ν - q) / (2 * ν ^ 2 - 1)
  let G : ℝ := ν - L / X
  let U : ℝ := ν ^ 6 / (2 * ν ^ 2 - 1) *
    (1 - (L - 1 / 2) / (X * ν)) * (1 - L / (X * ν))
  let E : ℝ := Real.exp ((591 / 100 : ℝ) * Real.sqrt X * Real.exp (-X))
  have hq : 0 ≤ q := div_nonneg (by linarith) hXp.le
  have hqν : q < ν := by
    have hqL : q < L / X := (div_lt_div_iff_of_pos_right hXp).2 (by linarith)
    exact hqL.trans hLX
  have hB : 0 < B := by dsimp [B]; linarith
  have hF : 0 < F := by
    dsimp [F]
    exact div_pos (mul_pos (pow_pos hνp _) (sub_pos.2 hqν)) hD
  have hG : 0 < G := sub_pos.2 hLX
  have hUeq : U = F * G := by
    dsimp [U, F, G, q]
    field_simp
  have hU : 0 ≤ U := by rw [hUeq]; positivity
  have hpoly : 0 < ν ^ 4 + ν ^ 3 + ν ^ 2 - ν - 1 := by
    have hp3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) hν9 3
    have hp4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) hν9 4
    norm_num at hν2 hp3 hp4
    linarith
  have hgap : 0 < B * (2 * ν ^ 2 - 1) - ν ^ 4 * (ν - q) := by
    have hid : B * (2 * ν ^ 2 - 1) - ν ^ 4 * (ν - q) =
        (1 - ν) * (ν ^ 4 + ν ^ 3 + ν ^ 2 - ν - 1) + q * (ν ^ 2 - 1) ^ 2 := by
      dsimp [B]; ring
    rw [hid]
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 hν1) hpoly)
      (mul_nonneg hq (sq_nonneg _))
  have hFB : F < B := by
    dsimp [F]
    apply (div_lt_iff₀ hD).2
    linarith
  have hGE : G * Real.exp ((591 / 25 : ℝ) * Real.sqrt X * Real.exp (-X)) < 1 := by
    have hGexp : G ≤ Real.exp (-L / X) := by
      have he := Real.add_one_le_exp (-L / X)
      dsimp [G]
      rw [neg_div] at he ⊢
      linarith
    calc
      _ ≤ Real.exp (-L / X) *
          Real.exp ((591 / 25 : ℝ) * Real.sqrt X * Real.exp (-X)) := by gcongr
      _ = Real.exp (-L / X + (591 / 25 : ℝ) * Real.sqrt X * Real.exp (-X)) :=
        (Real.exp_add _ _).symm
      _ < Real.exp 0 := by
        apply Real.exp_lt_exp.2
        rw [neg_div]
        linarith [DusartComparison.exponential_loss X L hX hL]
      _ = 1 := Real.exp_zero
  have hE4 : E ^ 4 = Real.exp ((591 / 25 : ℝ) * Real.sqrt X * Real.exp (-X)) := by
    dsimp [E]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hUE : U * E ^ 4 < B := by
    rw [hUeq, hE4]
    calc
      _ = F * (G * Real.exp ((591 / 25 : ℝ) * Real.sqrt X * Real.exp (-X))) := by ring
      _ < F * 1 := mul_lt_mul_of_pos_left hGE hF
      _ = F := mul_one _
      _ < B := hFB
  have hrootU : (Real.sqrt (Real.sqrt U)) ^ 4 = U := by
    calc
      _ = ((Real.sqrt (Real.sqrt U)) ^ 2) ^ 2 := by ring
      _ = U := by rw [Real.sq_sqrt (Real.sqrt_nonneg U), Real.sq_sqrt hU]
  have hrootB : (Real.sqrt (Real.sqrt B)) ^ 4 = B := by
    calc
      _ = ((Real.sqrt (Real.sqrt B)) ^ 2) ^ 2 := by ring
      _ = B := by rw [Real.sq_sqrt (Real.sqrt_nonneg B), Real.sq_sqrt hB.le]
  change Real.sqrt (Real.sqrt U) * E < Real.sqrt (Real.sqrt B)
  by_contra! hn
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg (Real.sqrt B)) hn 4
  rw [mul_pow, hrootU, hrootB] at hp
  linarith

