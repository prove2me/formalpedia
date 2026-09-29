-- Prove2me | solution 1 for CirclePackingConstants.n7_rep13_interval_stage_4
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:14:54.766169+00:00
-- url     : https://prove2.me/submissions/0c23b6d9-e38e-45b8-b40c-af806cb40caf

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
  (hx0L : (0:ℝ) ≤ x0) (hx0U : x0 ≤ (626:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (630:ℝ))
  (hx1L : (2002:ℝ) ≤ x1) (hx1U : x1 ≤ (2217:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (144:ℝ))
  (hx2L : (1285:ℝ) ≤ x2) (hx2U : x2 ≤ (1399:ℝ)) (hy2L : (1260:ℝ) ≤ y2) (hy2U : y2 ≤ (1399:ℝ))
  (hx3L : (2886:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1260:ℝ) ≤ y3) (hy3U : y3 ≤ (1400:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (110:ℝ)) (hy4L : (2052:ℝ) ≤ y4) (hy4U : y4 ≤ (2226:ℝ))
  (hx5L : (1258:ℝ) ≤ x5) (hx5U : x5 ≤ (1408:ℝ)) (hy5L : (2776:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2850:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2854:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (602:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (604:ℝ) ∧ (2122:ℝ) ≤ x1 ∧ x1 ≤ (2203:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (50:ℝ) ∧ (1325:ℝ) ≤ x2 ∧ x2 ≤ (1399:ℝ) ∧ (1314:ℝ) ≤ y2 ∧ y2 ≤ (1396:ℝ) ∧ (2930:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1316:ℝ) ≤ y3 ∧ y3 ≤ (1396:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (63:ℝ) ∧ (2106:ℝ) ≤ y4 ∧ y4 ≤ (2208:ℝ) ∧ (1336:ℝ) ≤ x5 ∧ x5 ≤ (1399:ℝ) ∧ (2918:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2941:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2920:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
  have u128 : y4 ≤ (2224:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1408:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact hx4U
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (776:ℝ)) (D := (1408:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2776:ℝ)) (bi := (2226:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u129 : (2861:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (141:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1601:ℝ)) (D := (141:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2776:ℝ)) (aj := (1260:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact hy2U) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u130 : (1298:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (948:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u129
      · exact hy5U
      · exact hy4L
      · exact u128
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1298:ℝ)) (D := (948:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1258:ℝ)) (aj := (0:ℝ)) (bj := (110:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5L) (by exact hx4U) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u131 : x5 ≤ (1399:ℝ) := by
    have hd : (y5-y6)^2 ≤ (146:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u129
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1601:ℝ)) (D := (146:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2850:ℝ)) (bi := (1408:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u132 : (2860:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (150:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1600:ℝ)) (D := (150:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2854:ℝ)) (aj := (1260:ℝ)) (bj := (1400:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact hy3U) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u133 : (2899:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (140:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u132
      · exact hy6U
      · exact u129
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1601:ℝ)) (D := (140:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2850:ℝ)) (aj := (1298:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u131) (by exact u130) (by norm_num)
    linarith only [hh]
  have u134 : x0 ≤ (607:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1399:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact hy0U
      · exact hy2L
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (792:ℝ)) (D := (1399:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1285:ℝ)) (bi := (626:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx0U) (by exact hx2L) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u135 : y0 ≤ (607:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1399:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u134
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (792:ℝ)) (D := (1399:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1260:ℝ)) (bi := (630:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u136 : (2077:ℝ) ≤ x1 := by
    have hd : (y1-y2)^2 ≤ (1399:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact hy2L
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (792:ℝ)) (D := (1399:ℝ))
      (xi := x1) (xj := x2) (yi := y1) (yj := y2)
      (ai := (2002:ℝ)) (aj := (1285:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1L) (by exact hx2U) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have u137 : y1 ≤ (90:ℝ) := by
    have hd : (x1-x2)^2 ≤ (932:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u136
      · exact hx1U
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y2)^2+(x1-x2)^2 := by nlinarith only [hT12]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1309:ℝ)) (D := (932:ℝ))
      (xi := y1) (xj := y2) (yi := x1) (yj := x2)
      (aj := (1260:ℝ)) (bi := (144:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy2L) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u138 : x1 ≤ (2210:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1400:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u137
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (790:ℝ)) (D := (1400:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2886:ℝ)) (bi := (2217:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u139 : y1 ≤ (84:ℝ) := by
    have hd : (x1-x3)^2 ≤ (923:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u136
      · exact u138
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1316:ℝ)) (D := (923:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1260:ℝ)) (bi := (90:ℝ)) (bj := (1400:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u137) (by exact hy3L) (by exact hy3U) (by norm_num)
    linarith only [hh]
  have u140 : (1314:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (925:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact hx2U
      · exact u136
      · exact u138
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1314:ℝ)) (D := (925:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1260:ℝ)) (aj := (0:ℝ)) (bj := (84:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2L) (by exact u139) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u141 : (1325:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (910:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u140
      · exact hy2U
      · exact hy4L
      · exact u128
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1325:ℝ)) (D := (910:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1285:ℝ)) (aj := (0:ℝ)) (bj := (110:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2L) (by exact hx4U) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u142 : y2 ≤ (1396:ℝ) := by
    have hd : (x2-x5)^2 ≤ (101:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u141
      · exact hx2U
      · exact u130
      · exact u131
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1604:ℝ)) (D := (101:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2861:ℝ)) (bi := (1399:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact u129) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u143 : (1316:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (923:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx3L
      · exact hx3U
      · exact u136
      · exact u138
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1316:ℝ)) (D := (923:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1260:ℝ)) (aj := (0:ℝ)) (bj := (84:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact u139) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u144 : (2930:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (86:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u143
      · exact hy3U
      · exact u140
      · exact u142
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1605:ℝ)) (D := (86:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2886:ℝ)) (aj := (1325:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact hx2U) (by exact u141) (by norm_num)
    linarith only [hh]
  have u145 : y3 ≤ (1396:ℝ) := by
    have hd : (x3-x6)^2 ≤ (101:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u144
      · exact hx3U
      · exact u133
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1604:ℝ)) (D := (101:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2860:ℝ)) (bi := (1400:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3U) (by exact u132) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u146 : x4 ≤ (74:ℝ) := by
    have hd : (y4-y2)^2 ≤ (910:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact u128
      · exact u140
      · exact u142
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x2)^2+(y4-y2)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1325:ℝ)) (D := (910:ℝ))
      (xi := x4) (xj := x2) (yi := y4) (yj := y2)
      (aj := (1325:ℝ)) (bi := (110:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact u141) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u147 : (2106:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1399:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u146
      · exact u141
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (792:ℝ)) (D := (1399:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2052:ℝ)) (aj := (1314:ℝ)) (bj := (1396:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4L) (by exact u142) (by exact u140) (by norm_num)
    linarith only [hh]
  have u148 : x4 ≤ (63:ℝ) := by
    have hd : (y4-y5)^2 ≤ (894:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u147
      · exact u128
      · exact u129
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1336:ℝ)) (D := (894:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1298:ℝ)) (bi := (74:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u146) (by exact u130) (by exact u131) (by norm_num)
    linarith only [hh]
  have u149 : y4 ≤ (2208:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1399:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u148
      · exact u130
      · exact u131
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (792:ℝ)) (D := (1399:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2861:ℝ)) (bi := (2224:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u128) (by exact u129) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u150 : (2918:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (101:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u130
      · exact u131
      · exact u141
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1604:ℝ)) (D := (101:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2861:ℝ)) (aj := (1314:ℝ)) (bj := (1396:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u129) (by exact u142) (by exact u140) (by norm_num)
    linarith only [hh]
  have u151 : (1336:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (894:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u150
      · exact hy5U
      · exact u147
      · exact u149
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1336:ℝ)) (D := (894:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1298:ℝ)) (aj := (0:ℝ)) (bj := (63:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u130) (by exact u148) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u152 : (2920:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (101:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u133
      · exact hx6U
      · exact u144
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1604:ℝ)) (D := (101:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2860:ℝ)) (aj := (1316:ℝ)) (bj := (1396:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u132) (by exact u145) (by exact u143) (by norm_num)
    linarith only [hh]
  have u153 : (2941:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (82:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u152
      · exact hy6U
      · exact u150
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1605:ℝ)) (D := (82:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2899:ℝ)) (aj := (1336:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u133) (by exact u131) (by exact u151) (by norm_num)
    linarith only [hh]
  have u154 : x0 ≤ (602:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1396:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact u135
      · exact u140
      · exact u142
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (797:ℝ)) (D := (1396:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1325:ℝ)) (bi := (607:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u134) (by exact u141) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u155 : y0 ≤ (604:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1399:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u154
      · exact u141
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (792:ℝ)) (D := (1399:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1314:ℝ)) (bi := (607:ℝ)) (bj := (1396:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u135) (by exact u140) (by exact u142) (by norm_num)
    linarith only [hh]
  have u156 : (2122:ℝ) ≤ x1 := by
    have hd : (y1-y2)^2 ≤ (1396:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u139
      · exact u140
      · exact u142
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (797:ℝ)) (D := (1396:ℝ))
      (xi := x1) (xj := x2) (yi := y1) (yj := y2)
      (ai := (2077:ℝ)) (aj := (1325:ℝ)) (bj := (1399:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u136) (by exact hx2U) (by exact u141) (by norm_num)
    linarith only [hh]
  have u157 : y1 ≤ (54:ℝ) := by
    have hd : (x1-x2)^2 ≤ (885:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u156
      · exact u138
      · exact u141
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y2)^2+(x1-x2)^2 := by nlinarith only [hT12]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1342:ℝ)) (D := (885:ℝ))
      (xi := y1) (xj := y2) (yi := x1) (yj := x2)
      (aj := (1314:ℝ)) (bi := (84:ℝ)) (bj := (1396:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u139) (by exact u140) (by exact u142) (by norm_num)
    linarith only [hh]
  have u158 : x1 ≤ (2203:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1396:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u157
      · exact u143
      · exact u145
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (797:ℝ)) (D := (1396:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2930:ℝ)) (bi := (2210:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u138) (by exact u144) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u159 : y1 ≤ (50:ℝ) := by
    have hd : (x1-x3)^2 ≤ (878:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u156
      · exact u158
      · exact u144
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1346:ℝ)) (D := (878:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1316:ℝ)) (bi := (54:ℝ)) (bj := (1396:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u157) (by exact u143) (by exact u145) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u154, hy0L, u155, u156, u158, hy1L, u159, u141, hx2U, u140, u142, u144, hx3U, u143, u145, hx4L, u148, u147, u149, u151, u131, u150, hy5U, u153, hx6U, u152, hy6U⟩
