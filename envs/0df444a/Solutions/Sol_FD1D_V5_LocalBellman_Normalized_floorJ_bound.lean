-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.floorJ_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:35.682847+00:00
-- url     : https://prove2.me/submissions/031fc89e-e3d0-4fcc-8417-f1a7f68c7414

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
namespace Normalized
private theorem floorJ_bound_large
    {K e : ℝ} (hK : 1 ≤ K) (heK : K ≤ e) :
    (K ^ 2 + e ^ 2) / 4 ≤ floorJ K e := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have he0 : 0 ≤ e := hKpos.le.trans heK
  have hK8 : 0 < K + 8 := by linarith
  have hden : 0 < K * (16 + K + e) := by positivity
  have hgap : 0 ≤ (e - K) * (K + 1) := by positivity
  have hfrac :
      24 * (K + 1) / (K + 8) ≤
        24 * (K + 1) * (K + e) /
          (K * (16 + K + e)) := by
    apply (div_le_div_iff₀ hK8 hden).2
    nlinarith
  have hcoefBase :
      2 * K + 6 - 24 * (K + 1) / (K + 8) ≤ 8 * K / 3 := by
    rw [← mul_le_mul_iff_of_pos_right hK8]
    field_simp [hK8.ne']
    nlinarith [mul_nonneg (sub_nonneg.mpr hK)
      (by linarith : 0 ≤ K + 36)]
  have hcoef :
      2 * K + 6 -
          24 * (K + 1) * (K + e) /
            (K * (16 + K + e)) ≤
        8 * K / 3 := by
    linarith
  have hlinear :=
    mul_le_mul_of_nonneg_right hcoef he0
  have hlinearLower :
      -(8 * K * e / 3) ≤
        -(2 * K + 6) * e +
          24 * (K + 1) * e * (K + e) /
            (K * (16 + K + e)) := by
    have hneg := neg_le_neg hlinear
    calc
      -(8 * K * e / 3) = -(8 * K / 3 * e) := by ring
      _ ≤ -((2 * K + 6 -
          24 * (K + 1) * (K + e) /
            (K * (16 + K + e))) * e) := hneg
      _ = -(2 * K + 6) * e +
          24 * (K + 1) * e * (K + e) /
            (K * (16 + K + e)) := by ring
  have hbase : 2 * K ^ 2 ≤ 5 * K ^ 2 - 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hK)
      (by linarith : 0 ≤ K + 1)]
  have hfirst :
      2 * K ^ 2 + 2 * e ^ 2 - 8 * K * e / 3 ≤
        floorJ K e := by
    unfold floorJ
    linarith
  have hsquare : 0 ≤ (K - e) ^ 2 := sq_nonneg _
  exact (by
    calc
      (K ^ 2 + e ^ 2) / 4
          ≤ 2 * K ^ 2 + 2 * e ^ 2 - 8 * K * e / 3 := by
            nlinarith
      _ ≤ floorJ K e := hfirst)
set_option maxHeartbeats 600000 in
private theorem floorJ_bound_small
    {K e : ℝ} (hK : 1 ≤ K) (he0 : 0 ≤ e) (heK : e ≤ K) :
    (K ^ 2 + e ^ 2) / 4 ≤ floorJ K e := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let ξ : ℝ := e / K
  let c : ℝ := 1 + ξ
  have hξ0 : 0 ≤ ξ := div_nonneg he0 hKpos.le
  have hξ1 : ξ ≤ 1 := (div_le_one hKpos).2 heK
  have hc1 : 1 ≤ c := by dsimp [c]; linarith
  have hc2 : c ≤ 2 := by dsimp [c]; linarith
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc1
  have hdenSmall : 0 < 16 + c := by linarith
  have hdenLarge : 0 < 16 + K * c := by positivity
  have hratio :
      2 / (16 + c) ≤ (K + 1) / (16 + K * c) := by
    apply (div_le_div_iff₀ hdenSmall hdenLarge).2
    have hprod :
        0 ≤ (K - 1) * (16 - c) :=
      mul_nonneg (sub_nonneg.mpr hK) (by linarith)
    nlinarith
  let B : ℝ := 6 - 48 * c / (16 + c)
  have hB : 2 / 3 ≤ B := by
    dsimp [B]
    rw [← mul_le_mul_iff_of_pos_right hdenSmall]
    field_simp [hdenSmall.ne']
    nlinarith
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 2 / 3).trans hB
  have hscaledRatio :
      48 * c / (16 + c) ≤
        24 * (K + 1) * c / (16 + K * c) := by
    calc
      48 * c / (16 + c) =
          (24 * c) * (2 / (16 + c)) := by ring
      _ ≤ (24 * c) * ((K + 1) / (16 + K * c)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 24 * (K + 1) * c / (16 + K * c) := by ring
  have hbracket :
      6 - 24 * (K + 1) * c / (16 + K * c) ≤ B := by
    dsimp [B]
    linarith
  have hξdiv : ξ / K ≤ ξ := by
    have honeDiv : 1 / K ≤ 1 := (div_le_one hKpos).2 hK
    calc
      ξ / K = ξ * (1 / K) := by ring
      _ ≤ ξ * 1 := mul_le_mul_of_nonneg_left honeDiv hξ0
      _ = ξ := by ring
  have hInvSq : 1 / K ^ 2 ≤ 1 := by
    have hKSq : 1 ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
    exact (div_le_one (sq_pos_of_pos hKpos)).2 hKSq
  have hidentity :
      floorJ K e / K ^ 2 =
        5 + 2 * ξ ^ 2 - 2 * ξ - 3 / K ^ 2 -
          ξ / K *
            (6 - 24 * (K + 1) * c / (16 + K * c)) := by
    dsimp [ξ, c]
    unfold floorJ
    field_simp [hKpos.ne', hdenLarge.ne']
    ring
  have hratioLower :
      2 + 2 * ξ ^ 2 - 8 * ξ +
          48 * ξ * (1 + ξ) / (17 + ξ) ≤
        floorJ K e / K ^ 2 := by
    rw [hidentity]
    have hmulBracket :=
      mul_le_mul_of_nonneg_left hbracket
        (div_nonneg hξ0 hKpos.le)
    have hmulB :=
      mul_le_mul_of_nonneg_right hξdiv hB0
    have hthree : 3 / K ^ 2 ≤ 3 := by
      calc
        3 / K ^ 2 = 3 * (1 / K ^ 2) := by ring
        _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left hInvSq (by norm_num)
        _ = 3 := by ring
    calc
      2 + 2 * ξ ^ 2 - 8 * ξ +
            48 * ξ * (1 + ξ) / (17 + ξ) =
          2 + 2 * ξ ^ 2 - 2 * ξ - ξ * B := by
            dsimp [B, c]
            ring
      _ ≤ 5 + 2 * ξ ^ 2 - 2 * ξ - 3 / K ^ 2 - ξ * B := by
        linarith
      _ ≤ 5 + 2 * ξ ^ 2 - 2 * ξ - 3 / K ^ 2 -
            ξ / K * B := by
        linarith
      _ ≤ 5 + 2 * ξ ^ 2 - 2 * ξ - 3 / K ^ 2 -
            ξ / K *
              (6 - 24 * (K + 1) * c / (16 + K * c)) := by
        linarith
  let j : ℝ :=
    2 + 2 * ξ ^ 2 - 8 * ξ +
      48 * ξ * (1 + ξ) / (17 + ξ)
  have hdenXi : 0 < 17 + ξ := by linarith
  have hpoly :
      0 ≤ 7 * ξ ^ 3 + 29 * (3 * ξ - 2) ^ 2 +
        18 * ξ ^ 2 + 3 * ξ + 3 := by positivity
  have hj :
      (1 + ξ ^ 2) / 4 ≤ j := by
    have hid :
        4 * (17 + ξ) * (j - (1 + ξ ^ 2) / 4) =
          7 * ξ ^ 3 + 29 * (3 * ξ - 2) ^ 2 +
            18 * ξ ^ 2 + 3 * ξ + 3 := by
      dsimp [j]
      field_simp [hdenXi.ne']
      ring
    have hnonneg :
        0 ≤ 4 * (17 + ξ) * (j - (1 + ξ ^ 2) / 4) := by
      rw [hid]
      exact hpoly
    have hfac : 0 < 4 * (17 + ξ) := by positivity
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hfac).mp hnonneg)
  have hnormalized :
      (1 + ξ ^ 2) / 4 ≤ floorJ K e / K ^ 2 :=
    hj.trans (by simpa [j] using hratioLower)
  have hKSqpos : 0 < K ^ 2 := sq_pos_of_pos hKpos
  have hscaled :=
    mul_le_mul_of_nonneg_left hnormalized hKSqpos.le
  have hleft :
      K ^ 2 * ((1 + ξ ^ 2) / 4) =
        (K ^ 2 + e ^ 2) / 4 := by
    dsimp [ξ]
    field_simp [hKpos.ne']
  have hright :
      K ^ 2 * (floorJ K e / K ^ 2) = floorJ K e := by
    field_simp [hKpos.ne']
  rwa [hleft, hright] at hscaled
end Normalized
end
end FD1D.V5.LocalBellman
end

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution
    {K e : ℝ} (hK : 1 ≤ K) (he0 : 0 ≤ e) :
    (K ^ 2 + e ^ 2) / 4 ≤ floorJ K e := by
  by_cases heK : K ≤ e
  · exact floorJ_bound_large hK heK
  · exact floorJ_bound_small hK he0 (le_of_not_ge heK)
end FD1D.V5.LocalBellman.Normalized
