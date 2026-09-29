-- Prove2me | solution 1 for CirclePackingConstants.n7_rep13_interval_stage_5
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:18:33.927541+00:00
-- url     : https://prove2.me/submissions/e42ded7c-f73b-4912-83af-b65147e587b9

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
  (hx0L : (0:ℝ) ≤ x0) (hx0U : x0 ≤ (602:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (604:ℝ))
  (hx1L : (2122:ℝ) ≤ x1) (hx1U : x1 ≤ (2203:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (50:ℝ))
  (hx2L : (1325:ℝ) ≤ x2) (hx2U : x2 ≤ (1399:ℝ)) (hy2L : (1314:ℝ) ≤ y2) (hy2U : y2 ≤ (1396:ℝ))
  (hx3L : (2930:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1316:ℝ) ≤ y3) (hy3U : y3 ≤ (1396:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (63:ℝ)) (hy4L : (2106:ℝ) ≤ y4) (hy4U : y4 ≤ (2208:ℝ))
  (hx5L : (1336:ℝ) ≤ x5) (hx5U : x5 ≤ (1399:ℝ)) (hy5L : (2918:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2941:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2920:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (595:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (595:ℝ) ∧ (2157:ℝ) ≤ x1 ∧ x1 ≤ (2200:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (26:ℝ) ∧ (1370:ℝ) ≤ x2 ∧ x2 ≤ (1394:ℝ) ∧ (1368:ℝ) ≤ y2 ∧ y2 ≤ (1393:ℝ) ∧ (2977:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1368:ℝ) ≤ y3 ∧ y3 ≤ (1393:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (20:ℝ) ∧ (2168:ℝ) ≤ y4 ∧ y4 ≤ (2201:ℝ) ∧ (1361:ℝ) ≤ x5 ∧ x5 ≤ (1395:ℝ) ∧ (2975:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2967:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2952:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
  have u160 : (1346:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (878:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact hx2U
      · exact hx1L
      · exact hx1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1346:ℝ)) (D := (878:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1314:ℝ)) (aj := (0:ℝ)) (bj := (50:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2L) (by exact hy1U) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u161 : x2 ≤ (1395:ℝ) := by
    have hd : (y2-y3)^2 ≤ (80:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u160
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1605:ℝ)) (D := (80:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2930:ℝ)) (bi := (1399:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u162 : (1357:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (862:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u160
      · exact hy2U
      · exact hy4L
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1357:ℝ)) (D := (862:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1325:ℝ)) (aj := (0:ℝ)) (bj := (63:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2L) (by exact hx4U) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u163 : y2 ≤ (1394:ℝ) := by
    have hd : (x2-x5)^2 ≤ (59:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u162
      · exact u161
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1606:ℝ)) (D := (59:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2918:ℝ)) (bi := (1396:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u164 : (1346:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (878:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx3L
      · exact hx3U
      · exact hx1L
      · exact hx1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1346:ℝ)) (D := (878:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1316:ℝ)) (aj := (0:ℝ)) (bj := (50:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact hy1U) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u165 : (2963:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (50:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u164
      · exact hy3U
      · exact u160
      · exact u163
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1606:ℝ)) (D := (50:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2930:ℝ)) (aj := (1357:ℝ)) (bj := (1395:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact u161) (by exact u162) (by norm_num)
    linarith only [hh]
  have u166 : y3 ≤ (1394:ℝ) := by
    have hd : (x3-x6)^2 ≤ (59:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u165
      · exact hx3U
      · exact hx6L
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1606:ℝ)) (D := (59:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2920:ℝ)) (bi := (1396:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u167 : x4 ≤ (38:ℝ) := by
    have hd : (y4-y2)^2 ≤ (862:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact hy4U
      · exact u160
      · exact u163
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x2)^2+(y4-y2)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1357:ℝ)) (D := (862:ℝ))
      (xi := x4) (xj := x2) (yi := y4) (yj := y2)
      (aj := (1357:ℝ)) (bi := (63:ℝ)) (bj := (1395:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact u162) (by exact u161) (by norm_num)
    linarith only [hh]
  have u168 : (2145:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1395:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u167
      · exact u162
      · exact u161
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (799:ℝ)) (D := (1395:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2106:ℝ)) (aj := (1346:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4L) (by exact u163) (by exact u160) (by norm_num)
    linarith only [hh]
  have u169 : (2952:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (59:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact u162
      · exact u161
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1606:ℝ)) (D := (59:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2918:ℝ)) (aj := (1346:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact u163) (by exact u160) (by norm_num)
    linarith only [hh]
  have u170 : (1361:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (855:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u169
      · exact hy5U
      · exact u168
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1361:ℝ)) (D := (855:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1336:ℝ)) (aj := (0:ℝ)) (bj := (38:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5L) (by exact u167) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u171 : x5 ≤ (1395:ℝ) := by
    have hd : (y5-y6)^2 ≤ (80:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u169
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1605:ℝ)) (D := (80:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2941:ℝ)) (bi := (1399:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u172 : (2952:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (59:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact u165
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1606:ℝ)) (D := (59:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2920:ℝ)) (aj := (1346:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact u166) (by exact u164) (by norm_num)
    linarith only [hh]
  have u173 : (2967:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (48:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u172
      · exact hy6U
      · exact u169
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1606:ℝ)) (D := (48:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2941:ℝ)) (aj := (1361:ℝ)) (bj := (1395:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u171) (by exact u170) (by norm_num)
    linarith only [hh]
  have u174 : x0 ≤ (595:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1394:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact hy0U
      · exact u160
      · exact u163
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (800:ℝ)) (D := (1394:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1357:ℝ)) (bi := (602:ℝ)) (bj := (1395:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx0U) (by exact u162) (by exact u161) (by norm_num)
    linarith only [hh]
  have u175 : y0 ≤ (595:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1395:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u174
      · exact u162
      · exact u161
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (799:ℝ)) (D := (1395:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1346:ℝ)) (bi := (604:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy0U) (by exact u160) (by exact u163) (by norm_num)
    linarith only [hh]
  have u176 : (2157:ℝ) ≤ x1 := by
    have hd : (y1-y2)^2 ≤ (1394:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact u160
      · exact u163
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (800:ℝ)) (D := (1394:ℝ))
      (xi := x1) (xj := x2) (yi := y1) (yj := y2)
      (ai := (2122:ℝ)) (aj := (1357:ℝ)) (bj := (1395:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1L) (by exact u161) (by exact u162) (by norm_num)
    linarith only [hh]
  have u177 : y1 ≤ (27:ℝ) := by
    have hd : (x1-x2)^2 ≤ (846:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u176
      · exact hx1U
      · exact u162
      · exact u161
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y2)^2+(x1-x2)^2 := by nlinarith only [hT12]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1367:ℝ)) (D := (846:ℝ))
      (xi := y1) (xj := y2) (yi := x1) (yj := x2)
      (aj := (1346:ℝ)) (bi := (50:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact u160) (by exact u163) (by norm_num)
    linarith only [hh]
  have u178 : x1 ≤ (2200:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1394:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u177
      · exact u164
      · exact u166
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (800:ℝ)) (D := (1394:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2963:ℝ)) (bi := (2203:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1U) (by exact u165) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u179 : y1 ≤ (26:ℝ) := by
    have hd : (x1-x3)^2 ≤ (843:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u176
      · exact u178
      · exact u165
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1368:ℝ)) (D := (843:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1346:ℝ)) (bi := (27:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u177) (by exact u164) (by exact u166) (by norm_num)
    linarith only [hh]
  have u180 : (1368:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (843:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u162
      · exact u161
      · exact u176
      · exact u178
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1368:ℝ)) (D := (843:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1346:ℝ)) (aj := (0:ℝ)) (bj := (26:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u160) (by exact u179) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u181 : x2 ≤ (1394:ℝ) := by
    have hd : (y2-y3)^2 ≤ (48:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u180
      · exact u163
      · exact u164
      · exact u166
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1606:ℝ)) (D := (48:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2963:ℝ)) (bi := (1395:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u161) (by exact u165) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u182 : (1370:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (840:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u180
      · exact u163
      · exact u168
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1370:ℝ)) (D := (840:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1357:ℝ)) (aj := (0:ℝ)) (bj := (38:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u162) (by exact u167) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u183 : y2 ≤ (1393:ℝ) := by
    have hd : (x2-x5)^2 ≤ (33:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u182
      · exact u181
      · exact u170
      · exact u171
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (33:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2952:ℝ)) (bi := (1394:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u163) (by exact u169) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u184 : (1368:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (843:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u165
      · exact hx3U
      · exact u176
      · exact u178
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1368:ℝ)) (D := (843:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1346:ℝ)) (aj := (0:ℝ)) (bj := (26:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u164) (by exact u179) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u185 : (2977:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (26:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u184
      · exact u166
      · exact u180
      · exact u183
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (26:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2963:ℝ)) (aj := (1370:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u165) (by exact u181) (by exact u182) (by norm_num)
    linarith only [hh]
  have u186 : y3 ≤ (1393:ℝ) := by
    have hd : (x3-x6)^2 ≤ (33:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u185
      · exact hx3U
      · exact u173
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (33:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2952:ℝ)) (bi := (1394:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u166) (by exact u172) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u187 : x4 ≤ (24:ℝ) := by
    have hd : (y4-y2)^2 ≤ (840:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u168
      · exact hy4U
      · exact u180
      · exact u183
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x2)^2+(y4-y2)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1370:ℝ)) (D := (840:ℝ))
      (xi := x4) (xj := x2) (yi := y4) (yj := y2)
      (aj := (1370:ℝ)) (bi := (38:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u167) (by exact u182) (by exact u181) (by norm_num)
    linarith only [hh]
  have u188 : (2168:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1394:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u187
      · exact u182
      · exact u181
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (800:ℝ)) (D := (1394:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2145:ℝ)) (aj := (1368:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u168) (by exact u183) (by exact u180) (by norm_num)
    linarith only [hh]
  have u189 : x4 ≤ (20:ℝ) := by
    have hd : (y4-y5)^2 ≤ (832:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u188
      · exact hy4U
      · exact u169
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1375:ℝ)) (D := (832:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1361:ℝ)) (bi := (24:ℝ)) (bj := (1395:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u187) (by exact u170) (by exact u171) (by norm_num)
    linarith only [hh]
  have u190 : y4 ≤ (2201:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1395:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u189
      · exact u170
      · exact u171
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (799:ℝ)) (D := (1395:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2952:ℝ)) (bi := (2208:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4U) (by exact u169) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u191 : (2975:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (33:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u170
      · exact u171
      · exact u182
      · exact u181
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (33:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2952:ℝ)) (aj := (1368:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u169) (by exact u183) (by exact u180) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u174, hy0L, u175, u176, u178, hy1L, u179, u182, u181, u180, u183, u185, hx3U, u184, u186, hx4L, u189, u188, u190, u170, u171, u191, hy5U, u173, hx6U, u172, hy6U⟩
