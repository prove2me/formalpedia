-- Prove2me | solution 1 for CirclePackingConstants.n7_rep13_interval_stage_3
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:13:06.161292+00:00
-- url     : https://prove2.me/submissions/8a8b193a-1f6c-45ef-8940-982c1ba8183a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
noncomputable section
namespace CirclePackingConstants

lemma sqdiff_bound_contract {x y Lx Ux Ly Uy D : ℝ}
    (hLx : Lx ≤ x) (hUx : x ≤ Ux) (hLy : Ly ≤ y) (hUy : y ≤ Uy)
    (hneg : -D ≤ Lx - Uy) (hpos : Ux - Ly ≤ D) : (x-y)^2 ≤ D^2 := by
  have h1 : -D ≤ x-y := by linarith
  have h2 : x-y ≤ D := by linarith
  have hD : 0 ≤ D := by nlinarith [hneg,hpos]
  have hp : 0 ≤ D-(x-y) := by linarith
  have hn : 0 ≤ D+(x-y) := by linarith
  nlinarith only [mul_nonneg hp hn]
lemma force_lower_contract {T q D xi xj yi yj ai aj bj : ℝ}
    (hq0 : 0 ≤ q) (hsep : T < (xi-xj)^2 + (yi-yj)^2) (hdy : (yi-yj)^2 ≤ D^2)
    (hqt : q^2 + D^2 ≤ T) (hxi : ai ≤ xi) (hxjU : xj ≤ bj) (hxjL : aj ≤ xj)
    (hgap : bj - q < ai) : aj + q < xi := by
  have hsq : q^2 < (xi-xj)^2 := by nlinarith only [hsep,hdy,hqt]
  by_cases hpos : 0 ≤ xi-xj
  · have hgt : q < xi-xj := by nlinarith only [hsq,hpos,hq0]
    linarith only [hgt,hxjL]
  · have hneg : xi-xj < -q := by nlinarith only [hsq,hpos,hq0]
    linarith only [hneg,hxjU,hxi,hgap]
lemma force_upper_contract {T q D xi xj yi yj aj bi bj : ℝ}
    (hq0 : 0 ≤ q) (hsep : T < (xi-xj)^2 + (yi-yj)^2) (hdy : (yi-yj)^2 ≤ D^2)
    (hqt : q^2 + D^2 ≤ T) (hxi : xi ≤ bi) (hxjL : aj ≤ xj) (hxjU : xj ≤ bj)
    (hgap : bi < aj + q) : xi < bj - q := by
  have hsq : q^2 < (xi-xj)^2 := by nlinarith only [hsep,hdy,hqt]
  by_cases hpos : 0 ≤ xi-xj
  · have hgt : q < xi-xj := by nlinarith only [hsq,hpos,hq0]
    linarith only [hgt,hxjL,hxi,hgap]
  · have hneg : xi-xj < -q := by nlinarith only [hsq,hpos,hq0]
    linarith only [hneg,hxjU]
end CirclePackingConstants

open CirclePackingConstants

theorem solution (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L : (0:ℝ) ≤ x0) (hx0U : x0 ≤ (712:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (716:ℝ))
  (hx1L : (2000:ℝ) ≤ x1) (hx1U : x1 ≤ (2228:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (152:ℝ))
  (hx2L : (1135:ℝ) ≤ x2) (hx2U : x2 ≤ (1424:ℝ)) (hy2L : (1094:ℝ) ≤ y2) (hy2U : y2 ≤ (1416:ℝ))
  (hx3L : (2772:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1258:ℝ) ≤ y3) (hy3U : y3 ≤ (1409:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (152:ℝ)) (hy4L : (2000:ℝ) ≤ y4) (hy4U : y4 ≤ (2228:ℝ))
  (hx5L : (1258:ℝ) ≤ x5) (hx5U : x5 ≤ (1409:ℝ)) (hy5L : (2772:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2849:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2849:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
  (hT01 : (2584683:ℝ) < (x0-x1)^2+(y0-y1)^2)
  (hT02 : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2)
  (hT03 : (2584683:ℝ) < (x0-x3)^2+(y0-y3)^2)
  (hT04 : (2584683:ℝ) < (x0-x4)^2+(y0-y4)^2)
  (hT05 : (2584683:ℝ) < (x0-x5)^2+(y0-y5)^2)
  (hT06 : (2584683:ℝ) < (x0-x6)^2+(y0-y6)^2)
  (hT12 : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2)
  (hT13 : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2)
  (hT14 : (2584683:ℝ) < (x1-x4)^2+(y1-y4)^2)
  (hT15 : (2584683:ℝ) < (x1-x5)^2+(y1-y5)^2)
  (hT16 : (2584683:ℝ) < (x1-x6)^2+(y1-y6)^2)
  (hT23 : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2)
  (hT24 : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2)
  (hT25 : (2584683:ℝ) < (x2-x5)^2+(y2-y5)^2)
  (hT26 : (2584683:ℝ) < (x2-x6)^2+(y2-y6)^2)
  (hT34 : (2584683:ℝ) < (x3-x4)^2+(y3-y4)^2)
  (hT35 : (2584683:ℝ) < (x3-x5)^2+(y3-y5)^2)
  (hT36 : (2584683:ℝ) < (x3-x6)^2+(y3-y6)^2)
  (hT45 : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2)
  (hT46 : (2584683:ℝ) < (x4-x6)^2+(y4-y6)^2)
  (hT56 : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2)
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (626:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (630:ℝ) ∧ (2002:ℝ) ≤ x1 ∧ x1 ≤ (2217:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (144:ℝ) ∧ (1285:ℝ) ≤ x2 ∧ x2 ≤ (1399:ℝ) ∧ (1260:ℝ) ≤ y2 ∧ y2 ≤ (1399:ℝ) ∧ (2886:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1260:ℝ) ≤ y3 ∧ y3 ≤ (1400:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (110:ℝ) ∧ (2052:ℝ) ≤ y4 ∧ y4 ≤ (2226:ℝ) ∧ (1258:ℝ) ≤ x5 ∧ x5 ≤ (1408:ℝ) ∧ (2776:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2850:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2854:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
  have u96 : x0 ≤ (663:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1416:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact hy0U
      · exact hy2L
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (761:ℝ)) (D := (1416:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1135:ℝ)) (bi := (712:ℝ)) (bj := (1424:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx0U) (by exact hx2L) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u97 : y0 ≤ (670:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1424:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u96
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (746:ℝ)) (D := (1424:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1094:ℝ)) (bi := (716:ℝ)) (bj := (1416:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u98 : x1 ≤ (2226:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1409:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (774:ℝ)) (D := (1409:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2772:ℝ)) (bi := (2228:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u99 : y1 ≤ (151:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact u98
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (152:ℝ)) (bj := (1409:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy3L) (by exact hy3U) (by norm_num)
    linarith only [hh]
  have u100 : (1180:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (1091:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact hx2U
      · exact hx1L
      · exact u98
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1180:ℝ)) (D := (1091:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1094:ℝ)) (aj := (0:ℝ)) (bj := (151:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2L) (by exact u99) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u101 : x2 ≤ (1409:ℝ) := by
    have hd : (y2-y3)^2 ≤ (229:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u100
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1591:ℝ)) (D := (229:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2772:ℝ)) (bi := (1424:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u102 : (1219:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (1048:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u100
      · exact hy2U
      · exact hy4L
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1219:ℝ)) (D := (1048:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1135:ℝ)) (aj := (0:ℝ)) (bj := (152:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2L) (by exact hx4U) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u103 : y2 ≤ (1404:ℝ) := by
    have hd : (x2-x5)^2 ≤ (190:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u102
      · exact u101
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1596:ℝ)) (D := (190:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2772:ℝ)) (bi := (1416:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u104 : (2774:ℝ) ≤ x3 := by
    have hd : (y3-y1)^2 ≤ (1409:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact hy1L
      · exact u99
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x1)^2+(y3-y1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (774:ℝ)) (D := (1409:ℝ))
      (xi := x3) (xj := x1) (yi := y3) (yj := y1)
      (ai := (2772:ℝ)) (aj := (2000:ℝ)) (bj := (2226:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact u98) (by exact hx1L) (by norm_num)
    linarith only [hh]
  have u105 : (2810:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (229:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact u100
      · exact u103
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1591:ℝ)) (D := (229:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2774:ℝ)) (aj := (1219:ℝ)) (bj := (1409:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u104) (by exact u101) (by exact u102) (by norm_num)
    linarith only [hh]
  have u106 : y3 ≤ (1404:ℝ) := by
    have hd : (x3-x6)^2 ≤ (190:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u105
      · exact hx3U
      · exact hx6L
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1596:ℝ)) (D := (190:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2849:ℝ)) (bi := (1409:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u107 : x4 ≤ (151:ℝ) := by
    have hd : (y4-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact hy4U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1258:ℝ)) (bi := (152:ℝ)) (bj := (1409:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
    linarith only [hh]
  have u108 : y4 ≤ (2226:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1409:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u107
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (774:ℝ)) (D := (1409:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2772:ℝ)) (bi := (2228:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u109 : (2776:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (190:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact u102
      · exact u101
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1596:ℝ)) (D := (190:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2772:ℝ)) (aj := (1180:ℝ)) (bj := (1404:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact u103) (by exact u100) (by norm_num)
    linarith only [hh]
  have u110 : x5 ≤ (1408:ℝ) := by
    have hd : (y5-y6)^2 ≤ (224:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u109
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1592:ℝ)) (D := (224:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2849:ℝ)) (bi := (1409:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u111 : (2854:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (190:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact u105
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1596:ℝ)) (D := (190:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2849:ℝ)) (aj := (1258:ℝ)) (bj := (1404:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact u106) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u112 : (2850:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (224:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u111
      · exact hy6U
      · exact u109
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1592:ℝ)) (D := (224:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2849:ℝ)) (aj := (1258:ℝ)) (bj := (1408:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u110) (by exact hx5L) (by norm_num)
    linarith only [hh]
  have u113 : x0 ≤ (626:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1404:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact u97
      · exact u100
      · exact u103
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (783:ℝ)) (D := (1404:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1219:ℝ)) (bi := (663:ℝ)) (bj := (1409:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u96) (by exact u102) (by exact u101) (by norm_num)
    linarith only [hh]
  have u114 : y0 ≤ (630:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1409:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u113
      · exact u102
      · exact u101
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (774:ℝ)) (D := (1409:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1180:ℝ)) (bi := (670:ℝ)) (bj := (1404:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u97) (by exact u100) (by exact u103) (by norm_num)
    linarith only [hh]
  have u115 : (2002:ℝ) ≤ x1 := by
    have hd : (y1-y2)^2 ≤ (1404:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u99
      · exact u100
      · exact u103
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (783:ℝ)) (D := (1404:ℝ))
      (xi := x1) (xj := x2) (yi := y1) (yj := y2)
      (ai := (2000:ℝ)) (aj := (1219:ℝ)) (bj := (1409:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1L) (by exact u101) (by exact u102) (by norm_num)
    linarith only [hh]
  have u116 : x1 ≤ (2217:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1404:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u99
      · exact hy3L
      · exact u106
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (783:ℝ)) (D := (1404:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2810:ℝ)) (bi := (2226:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u98) (by exact u105) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u117 : y1 ≤ (144:ℝ) := by
    have hd : (x1-x3)^2 ≤ (998:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u115
      · exact u116
      · exact u105
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1260:ℝ)) (D := (998:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (151:ℝ)) (bj := (1404:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u99) (by exact hy3L) (by exact u106) (by norm_num)
    linarith only [hh]
  have u118 : (1260:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (998:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u102
      · exact u101
      · exact u115
      · exact u116
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1260:ℝ)) (D := (998:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1180:ℝ)) (aj := (0:ℝ)) (bj := (144:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u100) (by exact u117) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u119 : x2 ≤ (1399:ℝ) := by
    have hd : (y2-y3)^2 ≤ (146:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u118
      · exact u103
      · exact hy3L
      · exact u106
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1601:ℝ)) (D := (146:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2810:ℝ)) (bi := (1409:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u101) (by exact u105) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u120 : (1285:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (966:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u118
      · exact u103
      · exact hy4L
      · exact u108
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1285:ℝ)) (D := (966:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1219:ℝ)) (aj := (0:ℝ)) (bj := (151:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u102) (by exact u107) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u121 : y2 ≤ (1399:ℝ) := by
    have hd : (x2-x5)^2 ≤ (141:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u120
      · exact u119
      · exact hx5L
      · exact u110
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1601:ℝ)) (D := (141:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2776:ℝ)) (bi := (1404:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u103) (by exact u109) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u122 : (1260:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (998:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u105
      · exact hx3U
      · exact u115
      · exact u116
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1260:ℝ)) (D := (998:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1258:ℝ)) (aj := (0:ℝ)) (bj := (144:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact u117) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u123 : (2886:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (144:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u122
      · exact u106
      · exact u118
      · exact u121
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1601:ℝ)) (D := (144:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2810:ℝ)) (aj := (1285:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u105) (by exact u119) (by exact u120) (by norm_num)
    linarith only [hh]
  have u124 : y3 ≤ (1400:ℝ) := by
    have hd : (x3-x6)^2 ≤ (150:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u123
      · exact hx3U
      · exact u112
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1600:ℝ)) (D := (150:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2854:ℝ)) (bi := (1404:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u106) (by exact u111) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u125 : x4 ≤ (114:ℝ) := by
    have hd : (y4-y2)^2 ≤ (966:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact u108
      · exact u118
      · exact u121
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x2)^2+(y4-y2)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1285:ℝ)) (D := (966:ℝ))
      (xi := x4) (xj := x2) (yi := y4) (yj := y2)
      (aj := (1285:ℝ)) (bi := (151:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u107) (by exact u120) (by exact u119) (by norm_num)
    linarith only [hh]
  have u126 : (2052:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1399:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u125
      · exact u120
      · exact u119
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (792:ℝ)) (D := (1399:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2000:ℝ)) (aj := (1260:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4L) (by exact u121) (by exact u118) (by norm_num)
    linarith only [hh]
  have u127 : x4 ≤ (110:ℝ) := by
    have hd : (y4-y5)^2 ≤ (948:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u126
      · exact u108
      · exact u109
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1298:ℝ)) (D := (948:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1258:ℝ)) (bi := (114:ℝ)) (bj := (1408:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u125) (by exact hx5L) (by exact u110) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u113, hy0L, u114, u115, u116, hy1L, u117, u120, u119, u118, u121, u123, hx3U, u122, u124, hx4L, u127, u126, u108, hx5L, u110, u109, hy5U, u112, hx6U, u111, hy6U⟩
