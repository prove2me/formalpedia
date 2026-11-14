-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.before_high_credit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:38.697723+00:00
-- url     : https://prove2.me/submissions/a34379ce-6770-4fc0-b888-bb759c5b5185

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackBeforeHigh

section

namespace ConsistentSubmodular.LowRollback

private theorem beta_positive (x q : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hL : 0 ≤ (1 - q) - (2 - q) * x) : 0 < beta x q := by
  let v := (1 - 2 * x) / (1 - x)
  have hden : 0 < 1 - x := by linarith
  have hv0 : 0 ≤ v := div_nonneg (by linarith) hden.le
  have hv1 : v ≤ 1 := by apply (div_le_one hden).mpr; linarith
  have hqv : q ≤ v := by apply (le_div_iff₀ hden).mpr; nlinarith
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx0 _
  have hx4 : x ^ 4 ≤ 1 / 16 := by
    have hh := pow_le_pow_left₀ hx0 hx1 4
    norm_num at hh
    exact hh
  have hx5 : 0 ≤ x ^ 5 := pow_nonneg hx0 _
  have hQ : 0 ≤ 11 * x ^ 3 - 14 * x ^ 2 - 12 * x + 12 := by nlinarith
  have hCx : 0 ≤ (1 - x) ^ 2 * (1 + x) := mul_nonneg (sq_nonneg _) (by linarith)
  have hbracket : 0 ≤
      (1 - x) ^ 2 * (1 + x) * (v ^ 2 + v * q + q ^ 2)-
      (11 * x ^ 3 - 14 * x ^ 2 - 12 * x + 12) * (v + q) + 4 * (1 - x ^ 2) * (13 - 10 * x) := by
    have hp := mul_nonneg hCx (show 0 ≤ v ^ 2 + v * q + q ^ 2 by positivity)
    have hq := mul_nonneg hQ (show 0 ≤ 2 - (v + q) by linarith)
    have hb : 14 ≤ 4 * (1 - x ^ 2) * (13 - 10 * x) - 2 * (11 * x ^ 3 - 14 * x ^ 2 - 12 * x + 12) := by
      nlinarith only [hx1, hx2, hx3]
    linarith
  have hmon : beta x v ≤ beta x q := by
    have heq : beta x q - beta x v = (v - q)*
        ((1 - x) ^ 2 * (1 + x) * (v ^ 2 + v * q + q ^ 2)-
        (11 * x ^ 3 - 14 * x ^ 2 - 12 * x + 12) * (v + q) + 4 * (1 - x ^ 2) * (13 - 10 * x)) := by
      unfold beta
      ring
    have hm := mul_nonneg (sub_nonneg.mpr hqv) hbracket
    linarith
  have hboundary : 0 < beta x v := by
    have heq : (1 - x) ^ 2 * beta x v = 4 * x ^ 5 - 8 * x ^ 4 + x ^ 3 - 5 * x ^ 2 - 2 * x + 7 := by
      dsimp [beta, v]
      field_simp
      ring
    have hp : 0 < 4 * x ^ 5 - 8 * x ^ 4 + x ^ 3 - 5 * x ^ 2 - 2 * x + 7 := by
      nlinarith only [hx5, hx4, hx3, hx2, hx1]
    have hden2 := sq_pos_of_pos hden
    exact (mul_pos_iff_of_pos_left hden2).mp (by rwa [heq])
  exact hboundary.trans_le hmon

end ConsistentSubmodular.LowRollback

end

section

open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (k q d₀ d p δ : ℝ)
    (hk2 : 2 ≤ k) (hk3 : k < 3) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hd : 0 < d) (hd₀ : 0 ≤ d₀) (hδ : 0 ≤ δ)
    (hI : 0 ≤ parentFloor k d₀ d p)
    (hR : 0 ≤ (5 - 3 * q) * d - p - dpoly q * δ)
    (hJ : 0 ≤ cpoly q * d - npoly q - apoly q * p - q ^ 2 * δ) :
    0 < VHigh k d₀ d p δ := by
  let x := k - 2
  let L := (1 - q) - (2 - q) * x
  let E := (1 - x) * q ^ 2 + (6 * x - 9) * q + 12 * (1 - x)
  let AI := (4 - q) * (4 - q - x ^ 2)
  let Nρ := q ^ 2 * (1 + x) + (2 - x) * x ^ 2 * (q - 3) ^ 2
  let Nγ := Nρ + x * E
  let Nη := -q ^ 2 * x ^ 2 + 3 * q ^ 2 * x + 8 * q * x ^ 2 - 21 * q * x + 2 * q - 20 * x ^ 2 + 36 * x + 8
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hx1 : x < 1 := by dsimp [x]; linarith
  have h1x : 0 < 1 - x := by linarith
  have h4k : 0 < 4 - k := by linarith
  have h2x : 0 < 2 - x := by linarith
  have hD : 0 < dpoly q := by unfold dpoly; nlinarith [sq_nonneg (q - 3 / 2)]
  have hL : 0 ≤ L := by
    have heq : (1 - x) * ((5 - 3 * q) * d - p - dpoly q * δ) + parentFloor k d₀ d p =
        3 * L * d - (1 - x) * dpoly q * δ - 2 * (2 - x) * d₀ := by
      dsimp [x, L, parentFloor, dpoly]
      ring
    have hsrc := mul_nonneg h1x.le hR
    have hp1 := mul_nonneg (mul_nonneg h1x.le hD.le) hδ
    have hp2 := mul_nonneg (show 0 ≤ 2 * (2 - x) by positivity) hd₀
    have hh : 0 ≤ 3 * L * d := by linarith only [heq, hsrc, hI, hp1, hp2]
    have := (mul_nonneg_iff_of_pos_right hd).mp hh
    linarith
  have hxhalf : x ≤ 1 / 2 := by
    have hm := mul_nonneg hq0.le h1x.le
    dsimp [L] at hL
    nlinarith
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hE : 0 < E := by
    have heq : (2 - q) * E = (q ^ 2 - 6 * q + 12) * L + 4 * dpoly q := by
      dsimp [E, L, dpoly]
      ring
    have hcoef : 0 ≤ q ^ 2 - 6 * q + 12 := by nlinarith [sq_nonneg (q - 3)]
    have hp := mul_nonneg hcoef hL
    apply (mul_pos_iff_of_pos_left (show 0 < 2 - q by linarith)).mp
    rw [heq]
    linarith
  have hn : 0 < npoly q := by
    unfold npoly
    exact mul_pos (by linarith) (sq_pos_of_ne_zero (by linarith))
  have hAI : 0 ≤ AI := by
    dsimp [AI]
    exact mul_nonneg (by linarith) (by nlinarith)
  have hNρ : 0 < Nρ := by
    dsimp [Nρ]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sq_pos_of_pos hq0) (by linarith))
      (mul_nonneg (mul_nonneg h2x.le (sq_nonneg x)) (sq_nonneg _))
  have hNγ : 0 ≤ Nγ := by dsimp [Nγ]; positivity
  have hNη : 0 ≤ Nη := by
    have heq : Nη = 8 + 5 * x + 20 * x * (1 / 2 - x) + q ^ 2 * x * (3 - x) + 8 * q * x ^ 2 + 2 * q + 21 * x * (1 - q) := by
      dsimp [Nη]
      ring
    have hxhalf' : 0 ≤ 1 / 2 - x := by linarith
    have h3x : 0 ≤ 3 - x := by linarith
    have hqone : 0 ≤ 1 - q := by linarith
    rw [heq]
    positivity
  have hbeta := beta_positive x q hx0 hxhalf hq0.le hq1 hL
  have heq : npoly q * E * VHigh k d₀ d p δ =
      npoly q * AI * parentFloor k d₀ d p+
      beta x q * ((5 - 3 * q) * d - p - dpoly q * δ)+
      Nγ * (cpoly q * d - npoly q - apoly q * p - q ^ 2 * δ)+
      npoly q * (4 - k) * Nη * d₀ + npoly q * Nρ := by
    dsimp [npoly, E, VHigh, AI, parentFloor, beta, dpoly, Nγ, Nρ, Nη, cpoly, apoly, x]
    ring
  have hfirst := mul_nonneg (mul_nonneg hn.le hAI) hI
  have hsecond := mul_nonneg hbeta.le hR
  have hthird := mul_nonneg hNγ hJ
  have hfourth := mul_nonneg (mul_nonneg (mul_nonneg hn.le h4k.le) hNη) hd₀
  have hlast := mul_pos hn hNρ
  have hh : 0 < npoly q * E * VHigh k d₀ d p δ := by
    rw [heq]
    linarith only [hfirst, hsecond, hthird, hfourth, hlast]
  exact (mul_pos_iff_of_pos_left (mul_pos hn hE)).mp hh

end
