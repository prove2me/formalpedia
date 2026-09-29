-- Prove2me | solution 1 for CirclePackingConstants.n7_rep13_interval_stage_2
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:04:39.962979+00:00
-- url     : https://prove2.me/submissions/f126e17a-0fda-44a0-a4b5-4eb4183010d2

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
  (hx0L : (0:ℝ) ≤ x0) (hx0U : x0 ≤ (775:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (775:ℝ))
  (hx1L : (2000:ℝ) ≤ x1) (hx1U : x1 ≤ (2249:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (163:ℝ))
  (hx2L : (1000:ℝ) ≤ x2) (hx2U : x2 ≤ (1446:ℝ)) (hy2L : (1012:ℝ) ≤ y2) (hy2U : y2 ≤ (1449:ℝ))
  (hx3L : (2751:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1258:ℝ) ≤ y3) (hy3U : y3 ≤ (1412:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (163:ℝ)) (hy4L : (2000:ℝ) ≤ y4) (hy4U : y4 ≤ (2249:ℝ))
  (hx5L : (1258:ℝ) ≤ x5) (hx5U : x5 ≤ (1412:ℝ)) (hy5L : (2751:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2846:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2846:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (712:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (716:ℝ) ∧ (2000:ℝ) ≤ x1 ∧ x1 ≤ (2228:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (152:ℝ) ∧ (1135:ℝ) ≤ x2 ∧ x2 ≤ (1424:ℝ) ∧ (1094:ℝ) ≤ y2 ∧ y2 ≤ (1416:ℝ) ∧ (2772:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1258:ℝ) ≤ y3 ∧ y3 ≤ (1409:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (152:ℝ) ∧ (2000:ℝ) ≤ y4 ∧ y4 ≤ (2228:ℝ) ∧ (1258:ℝ) ≤ x5 ∧ x5 ≤ (1409:ℝ) ∧ (2772:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2849:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2849:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
  have u64 : x0 ≤ (750:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1449:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact hy0U
      · exact hy2L
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (696:ℝ)) (D := (1449:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1000:ℝ)) (bi := (775:ℝ)) (bj := (1446:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx0U) (by exact hx2L) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u65 : y0 ≤ (747:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1446:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u64
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (702:ℝ)) (D := (1446:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1012:ℝ)) (bi := (775:ℝ)) (bj := (1449:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u66 : x1 ≤ (2232:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1412:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (768:ℝ)) (D := (1412:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2751:ℝ)) (bi := (2249:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u67 : y1 ≤ (154:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact u66
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (163:ℝ)) (bj := (1412:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy3L) (by exact hy3U) (by norm_num)
    linarith only [hh]
  have u68 : (1032:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (1232:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact hx2U
      · exact hx1L
      · exact u66
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1032:ℝ)) (D := (1232:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1012:ℝ)) (aj := (0:ℝ)) (bj := (154:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2L) (by exact u67) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u69 : x2 ≤ (1438:ℝ) := by
    have hd : (y2-y3)^2 ≤ (380:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u68
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1562:ℝ)) (D := (380:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2751:ℝ)) (bi := (1446:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u70 : (1050:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (1217:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u68
      · exact hy2U
      · exact hy4L
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1050:ℝ)) (D := (1217:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (163:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2L) (by exact hx4U) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u71 : y2 ≤ (1434:ℝ) := by
    have hd : (x2-x5)^2 ≤ (362:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u70
      · exact u69
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1566:ℝ)) (D := (362:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2751:ℝ)) (bi := (1449:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u72 : (2768:ℝ) ≤ x3 := by
    have hd : (y3-y1)^2 ≤ (1412:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact hy1L
      · exact u67
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x1)^2+(y3-y1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (768:ℝ)) (D := (1412:ℝ))
      (xi := x3) (xj := x1) (yi := y3) (yj := y1)
      (ai := (2751:ℝ)) (aj := (2000:ℝ)) (bj := (2232:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact u66) (by exact hx1L) (by norm_num)
    linarith only [hh]
  have u73 : y3 ≤ (1410:ℝ) := by
    have hd : (x3-x6)^2 ≤ (232:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u72
      · exact hx3U
      · exact hx6L
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1590:ℝ)) (D := (232:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2846:ℝ)) (bi := (1412:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u74 : x4 ≤ (154:ℝ) := by
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
      (aj := (1258:ℝ)) (bi := (163:ℝ)) (bj := (1412:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
    linarith only [hh]
  have u75 : y4 ≤ (2232:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1412:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u74
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (768:ℝ)) (D := (1412:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2751:ℝ)) (bi := (2249:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u76 : (2768:ℝ) ≤ y5 := by
    have hd : (x5-x4)^2 ≤ (1412:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact hx4L
      · exact u74
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y4)^2+(x5-x4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (768:ℝ)) (D := (1412:ℝ))
      (xi := y5) (xj := y4) (yi := x5) (yj := x4)
      (ai := (2751:ℝ)) (aj := (2000:ℝ)) (bj := (2232:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact u75) (by exact hy4L) (by norm_num)
    linarith only [hh]
  have u77 : x5 ≤ (1410:ℝ) := by
    have hd : (y5-y6)^2 ≤ (232:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u76
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1590:ℝ)) (D := (232:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2846:ℝ)) (bi := (1412:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u78 : (2848:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (232:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact u72
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1590:ℝ)) (D := (232:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2846:ℝ)) (aj := (1258:ℝ)) (bj := (1410:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact u73) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u79 : (2848:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (232:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u78
      · exact hy6U
      · exact u76
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1590:ℝ)) (D := (232:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2846:ℝ)) (aj := (1258:ℝ)) (bj := (1410:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u77) (by exact hx5L) (by norm_num)
    linarith only [hh]
  have u80 : x0 ≤ (712:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1434:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact u65
      · exact u68
      · exact u71
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (726:ℝ)) (D := (1434:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1050:ℝ)) (bi := (750:ℝ)) (bj := (1438:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u64) (by exact u70) (by exact u69) (by norm_num)
    linarith only [hh]
  have u81 : y0 ≤ (716:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1438:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u80
      · exact u70
      · exact u69
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (718:ℝ)) (D := (1438:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1032:ℝ)) (bi := (747:ℝ)) (bj := (1434:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u65) (by exact u68) (by exact u71) (by norm_num)
    linarith only [hh]
  have u82 : x1 ≤ (2228:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1410:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u67
      · exact hy3L
      · exact u73
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (772:ℝ)) (D := (1410:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2768:ℝ)) (bi := (2232:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u66) (by exact u72) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u83 : y1 ≤ (152:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact u82
      · exact u72
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (154:ℝ)) (bj := (1410:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u67) (by exact hy3L) (by exact u73) (by norm_num)
    linarith only [hh]
  have u84 : (1094:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (1178:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u70
      · exact u69
      · exact hx1L
      · exact u82
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1094:ℝ)) (D := (1178:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1032:ℝ)) (aj := (0:ℝ)) (bj := (152:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u68) (by exact u83) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u85 : x2 ≤ (1424:ℝ) := by
    have hd : (y2-y3)^2 ≤ (316:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u84
      · exact u71
      · exact hy3L
      · exact u73
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1576:ℝ)) (D := (316:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2768:ℝ)) (bi := (1438:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u69) (by exact u72) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u86 : (1135:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (1138:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u84
      · exact u71
      · exact hy4L
      · exact u75
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1135:ℝ)) (D := (1138:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1050:ℝ)) (aj := (0:ℝ)) (bj := (154:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u70) (by exact u74) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u87 : y2 ≤ (1416:ℝ) := by
    have hd : (x2-x5)^2 ≤ (275:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u86
      · exact u85
      · exact hx5L
      · exact u77
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1584:ℝ)) (D := (275:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2768:ℝ)) (bi := (1434:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u71) (by exact u76) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u88 : (2772:ℝ) ≤ x3 := by
    have hd : (y3-y1)^2 ≤ (1410:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact u73
      · exact hy1L
      · exact u83
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x1)^2+(y3-y1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (772:ℝ)) (D := (1410:ℝ))
      (xi := x3) (xj := x1) (yi := y3) (yj := y1)
      (ai := (2768:ℝ)) (aj := (2000:ℝ)) (bj := (2228:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u72) (by exact u82) (by exact hx1L) (by norm_num)
    linarith only [hh]
  have u89 : y3 ≤ (1409:ℝ) := by
    have hd : (x3-x6)^2 ≤ (228:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u88
      · exact hx3U
      · exact u79
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1591:ℝ)) (D := (228:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2848:ℝ)) (bi := (1410:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u73) (by exact u78) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u90 : x4 ≤ (152:ℝ) := by
    have hd : (y4-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact u75
      · exact u76
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1258:ℝ)) (bi := (154:ℝ)) (bj := (1410:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u74) (by exact hx5L) (by exact u77) (by norm_num)
    linarith only [hh]
  have u91 : y4 ≤ (2228:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1410:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u90
      · exact hx5L
      · exact u77
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (772:ℝ)) (D := (1410:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2768:ℝ)) (bi := (2232:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u75) (by exact u76) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u92 : (2772:ℝ) ≤ y5 := by
    have hd : (x5-x4)^2 ≤ (1410:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact u77
      · exact hx4L
      · exact u90
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y4)^2+(x5-x4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (772:ℝ)) (D := (1410:ℝ))
      (xi := y5) (xj := y4) (yi := x5) (yj := x4)
      (ai := (2768:ℝ)) (aj := (2000:ℝ)) (bj := (2228:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u76) (by exact u91) (by exact hy4L) (by norm_num)
    linarith only [hh]
  have u93 : x5 ≤ (1409:ℝ) := by
    have hd : (y5-y6)^2 ≤ (228:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u92
      · exact hy5U
      · exact u78
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1591:ℝ)) (D := (228:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2848:ℝ)) (bi := (1410:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u77) (by exact u79) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u94 : (2849:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (228:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u79
      · exact hx6U
      · exact u88
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1591:ℝ)) (D := (228:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2848:ℝ)) (aj := (1258:ℝ)) (bj := (1409:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u78) (by exact u89) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u95 : (2849:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (228:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u94
      · exact hy6U
      · exact u92
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1591:ℝ)) (D := (228:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2848:ℝ)) (aj := (1258:ℝ)) (bj := (1409:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u79) (by exact u93) (by exact hx5L) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u80, hy0L, u81, hx1L, u82, hy1L, u83, u86, u85, u84, u87, u88, hx3U, hy3L, u89, hx4L, u90, hy4L, u91, hx5L, u93, u92, hy5U, u95, hx6U, u94, hy6U⟩
