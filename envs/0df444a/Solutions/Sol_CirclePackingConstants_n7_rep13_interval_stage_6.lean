-- Prove2me | solution 1 for CirclePackingConstants.n7_rep13_interval_stage_6
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:20:29.281324+00:00
-- url     : https://prove2.me/submissions/796e453c-b273-4a49-8917-34733b346e59

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
  (hx0L : (0:ℝ) ≤ x0) (hx0U : x0 ≤ (595:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (595:ℝ))
  (hx1L : (2157:ℝ) ≤ x1) (hx1U : x1 ≤ (2200:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (26:ℝ))
  (hx2L : (1370:ℝ) ≤ x2) (hx2U : x2 ≤ (1394:ℝ)) (hy2L : (1368:ℝ) ≤ y2) (hy2U : y2 ≤ (1393:ℝ))
  (hx3L : (2977:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1368:ℝ) ≤ y3) (hy3U : y3 ≤ (1393:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (20:ℝ)) (hy4L : (2168:ℝ) ≤ y4) (hy4U : y4 ≤ (2201:ℝ))
  (hx5L : (1361:ℝ) ≤ x5) (hx5U : x5 ≤ (1395:ℝ)) (hy5L : (2975:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2967:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2952:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (591:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (591:ℝ) ∧ (2183:ℝ) ≤ x1 ∧ x1 ≤ (2198:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (9:ℝ) ∧ (1385:ℝ) ≤ x2 ∧ x2 ≤ (1393:ℝ) ∧ (1384:ℝ) ≤ y2 ∧ y2 ≤ (1393:ℝ) ∧ (2992:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1384:ℝ) ≤ y3 ∧ y3 ≤ (1393:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (8:ℝ) ∧ (2180:ℝ) ≤ y4 ∧ y4 ≤ (2200:ℝ) ∧ (1382:ℝ) ≤ x5 ∧ x5 ≤ (1393:ℝ) ∧ (2985:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2989:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2985:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
  have u192 : (1375:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (832:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy5L
      · exact hy5U
      · exact hy4L
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1375:ℝ)) (D := (832:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1361:ℝ)) (aj := (0:ℝ)) (bj := (20:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5L) (by exact hx4U) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u193 : x5 ≤ (1394:ℝ) := by
    have hd : (y5-y6)^2 ≤ (48:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy5L
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1606:ℝ)) (D := (48:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2967:ℝ)) (bi := (1395:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u194 : (2975:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (33:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (33:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2952:ℝ)) (aj := (1368:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact hy3U) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u195 : (2982:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (25:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u194
      · exact hy6U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (25:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2967:ℝ)) (aj := (1375:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u193) (by exact u192) (by norm_num)
    linarith only [hh]
  have u196 : x0 ≤ (592:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact hy0U
      · exact hy2L
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1370:ℝ)) (bi := (595:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx0U) (by exact hx2L) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u197 : y0 ≤ (593:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1394:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u196
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (800:ℝ)) (D := (1394:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1368:ℝ)) (bi := (595:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u198 : (2172:ℝ) ≤ x1 := by
    have hd : (y1-y2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact hy2L
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := x1) (xj := x2) (yi := y1) (yj := y2)
      (ai := (2157:ℝ)) (aj := (1370:ℝ)) (bj := (1394:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1L) (by exact hx2U) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have u199 : y1 ≤ (17:ℝ) := by
    have hd : (x1-x2)^2 ≤ (830:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u198
      · exact hx1U
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y2)^2+(x1-x2)^2 := by nlinarith only [hT12]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1376:ℝ)) (D := (830:ℝ))
      (xi := y1) (xj := y2) (yi := x1) (yj := x2)
      (aj := (1368:ℝ)) (bi := (26:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy2L) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u200 : x1 ≤ (2198:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u199
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2977:ℝ)) (bi := (2200:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u201 : y1 ≤ (15:ℝ) := by
    have hd : (x1-x3)^2 ≤ (828:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u198
      · exact u200
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1378:ℝ)) (D := (828:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1368:ℝ)) (bi := (17:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u199) (by exact hy3L) (by exact hy3U) (by norm_num)
    linarith only [hh]
  have u202 : (1378:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (828:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact hx2U
      · exact u198
      · exact u200
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1378:ℝ)) (D := (828:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1368:ℝ)) (aj := (0:ℝ)) (bj := (15:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2L) (by exact u201) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u203 : x2 ≤ (1393:ℝ) := by
    have hd : (y2-y3)^2 ≤ (25:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u202
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (25:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2977:ℝ)) (bi := (1394:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u204 : (1381:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (823:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u202
      · exact hy2U
      · exact hy4L
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1381:ℝ)) (D := (823:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1370:ℝ)) (aj := (0:ℝ)) (bj := (20:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2L) (by exact hx4U) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u205 : (1378:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (828:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx3L
      · exact hx3U
      · exact u198
      · exact u200
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1378:ℝ)) (D := (828:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1368:ℝ)) (aj := (0:ℝ)) (bj := (15:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact u201) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u206 : (2988:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (15:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u205
      · exact hy3U
      · exact u202
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (15:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2977:ℝ)) (aj := (1381:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact u203) (by exact u204) (by norm_num)
    linarith only [hh]
  have u207 : x4 ≤ (12:ℝ) := by
    have hd : (y4-y2)^2 ≤ (823:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact hy4U
      · exact u202
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x2)^2+(y4-y2)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1381:ℝ)) (D := (823:ℝ))
      (xi := x4) (xj := x2) (yi := y4) (yj := y2)
      (aj := (1381:ℝ)) (bi := (20:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact u204) (by exact u203) (by norm_num)
    linarith only [hh]
  have u208 : (2180:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u207
      · exact u204
      · exact u203
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2168:ℝ)) (aj := (1378:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4L) (by exact hy2U) (by exact u202) (by norm_num)
    linarith only [hh]
  have u209 : y4 ≤ (2200:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1394:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u207
      · exact u192
      · exact u193
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (800:ℝ)) (D := (1394:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2975:ℝ)) (bi := (2201:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u210 : (2985:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (18:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u192
      · exact u193
      · exact u204
      · exact u203
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (18:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2975:ℝ)) (aj := (1378:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact hy2U) (by exact u202) (by norm_num)
    linarith only [hh]
  have u211 : (1382:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (820:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u210
      · exact hy5U
      · exact u208
      · exact u209
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1382:ℝ)) (D := (820:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1375:ℝ)) (aj := (0:ℝ)) (bj := (12:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u192) (by exact u207) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u212 : x5 ≤ (1393:ℝ) := by
    have hd : (y5-y6)^2 ≤ (25:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u210
      · exact hy5U
      · exact u194
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (25:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2982:ℝ)) (bi := (1394:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u193) (by exact u195) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u213 : (2985:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (18:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u195
      · exact hx6U
      · exact u206
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (18:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2975:ℝ)) (aj := (1378:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u194) (by exact hy3U) (by exact u205) (by norm_num)
    linarith only [hh]
  have u214 : (2989:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (15:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u213
      · exact hy6U
      · exact u210
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (15:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2982:ℝ)) (aj := (1382:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u195) (by exact u212) (by exact u211) (by norm_num)
    linarith only [hh]
  have u215 : x0 ≤ (591:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact u197
      · exact u202
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1381:ℝ)) (bi := (592:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u196) (by exact u204) (by exact u203) (by norm_num)
    linarith only [hh]
  have u216 : y0 ≤ (591:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u215
      · exact u204
      · exact u203
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1378:ℝ)) (bi := (593:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u197) (by exact u202) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u217 : (2183:ℝ) ≤ x1 := by
    have hd : (y1-y2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u201
      · exact u202
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := x1) (xj := x2) (yi := y1) (yj := y2)
      (ai := (2172:ℝ)) (aj := (1381:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u198) (by exact u203) (by exact u204) (by norm_num)
    linarith only [hh]
  have u218 : y1 ≤ (9:ℝ) := by
    have hd : (x1-x2)^2 ≤ (817:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u217
      · exact u200
      · exact u204
      · exact u203
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y2)^2+(x1-x2)^2 := by nlinarith only [hT12]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1384:ℝ)) (D := (817:ℝ))
      (xi := y1) (xj := y2) (yi := x1) (yj := x2)
      (aj := (1378:ℝ)) (bi := (15:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u201) (by exact u202) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u219 : (1384:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (817:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u204
      · exact u203
      · exact u217
      · exact u200
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1384:ℝ)) (D := (817:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1378:ℝ)) (aj := (0:ℝ)) (bj := (9:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u202) (by exact u218) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u220 : (1385:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (816:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u219
      · exact hy2U
      · exact u208
      · exact u209
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1385:ℝ)) (D := (816:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1381:ℝ)) (aj := (0:ℝ)) (bj := (12:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u204) (by exact u207) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u221 : (1384:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (817:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u206
      · exact hx3U
      · exact u217
      · exact u200
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1384:ℝ)) (D := (817:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1378:ℝ)) (aj := (0:ℝ)) (bj := (9:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u205) (by exact u218) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u222 : (2992:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (9:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u221
      · exact hy3U
      · exact u219
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (9:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2988:ℝ)) (aj := (1385:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u206) (by exact u203) (by exact u220) (by norm_num)
    linarith only [hh]
  have u223 : x4 ≤ (8:ℝ) := by
    have hd : (y4-y2)^2 ≤ (816:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u208
      · exact u209
      · exact u219
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x2)^2+(y4-y2)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1385:ℝ)) (D := (816:ℝ))
      (xi := x4) (xj := x2) (yi := y4) (yj := y2)
      (aj := (1385:ℝ)) (bi := (12:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u207) (by exact u220) (by exact u203) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u215, hy0L, u216, u217, u200, hy1L, u218, u220, u203, u219, hy2U, u222, hx3U, u221, hy3U, hx4L, u223, u208, u209, u211, u212, u210, hy5U, u214, hx6U, u213, hy6U⟩
