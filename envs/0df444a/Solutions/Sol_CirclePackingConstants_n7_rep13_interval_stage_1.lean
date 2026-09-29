-- Prove2me | solution 1 for CirclePackingConstants.n7_rep13_interval_stage_1
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:02:43.110346+00:00
-- url     : https://prove2.me/submissions/b72e2825-d755-41c4-a324-044bffa38234

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
  (hx0L : (0:ℝ) ≤ x0) (hx0U : x0 ≤ (1000:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (1000:ℝ))
  (hx1L : (2000:ℝ) ≤ x1) (hx1U : x1 ≤ (2419:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (241:ℝ))
  (hx2L : (1000:ℝ) ≤ x2) (hx2U : x2 ≤ (1472:ℝ)) (hy2L : (1000:ℝ) ≤ y2) (hy2U : y2 ≤ (1472:ℝ))
  (hx3L : (2581:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1258:ℝ) ≤ y3) (hy3U : y3 ≤ (1448:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (241:ℝ)) (hy4L : (2000:ℝ) ≤ y4) (hy4U : y4 ≤ (2419:ℝ))
  (hx5L : (1258:ℝ) ≤ x5) (hx5U : x5 ≤ (1499:ℝ)) (hy5L : (2581:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2759:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2759:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (775:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (775:ℝ) ∧ (2000:ℝ) ≤ x1 ∧ x1 ≤ (2249:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (163:ℝ) ∧ (1000:ℝ) ≤ x2 ∧ x2 ≤ (1446:ℝ) ∧ (1012:ℝ) ≤ y2 ∧ y2 ≤ (1449:ℝ) ∧ (2751:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1258:ℝ) ≤ y3 ∧ y3 ≤ (1412:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (163:ℝ) ∧ (2000:ℝ) ≤ y4 ∧ y4 ≤ (2249:ℝ) ∧ (1258:ℝ) ≤ x5 ∧ x5 ≤ (1412:ℝ) ∧ (2751:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2846:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2846:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
  have u32 : x5 ≤ (1448:ℝ) := by
    have hd : (y5-y6)^2 ≤ (419:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy5L
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1552:ℝ)) (D := (419:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2759:ℝ)) (bi := (1499:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u33 : (2810:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (419:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1552:ℝ)) (D := (419:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2759:ℝ)) (aj := (1258:ℝ)) (bj := (1448:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact hy3U) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u34 : (2810:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (419:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u33
      · exact hy6U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1552:ℝ)) (D := (419:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2759:ℝ)) (aj := (1258:ℝ)) (bj := (1448:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u32) (by exact hx5L) (by norm_num)
    linarith only [hh]
  have u35 : x0 ≤ (826:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1472:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact hy0U
      · exact hy2L
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (646:ℝ)) (D := (1472:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1000:ℝ)) (bi := (1000:ℝ)) (bj := (1472:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx0U) (by exact hx2L) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u36 : y0 ≤ (826:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1472:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u35
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (646:ℝ)) (D := (1472:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1000:ℝ)) (bi := (1000:ℝ)) (bj := (1472:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u37 : x1 ≤ (2302:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1448:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (698:ℝ)) (D := (1448:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2581:ℝ)) (bi := (2419:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u38 : y1 ≤ (190:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact u37
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (241:ℝ)) (bj := (1448:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy3L) (by exact hy3U) (by norm_num)
    linarith only [hh]
  have u39 : x2 ≤ (1456:ℝ) := by
    have hd : (y2-y3)^2 ≤ (448:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy2L
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1544:ℝ)) (D := (448:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2581:ℝ)) (bi := (1472:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u40 : y2 ≤ (1456:ℝ) := by
    have hd : (x2-x5)^2 ≤ (448:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u39
      · exact hx5L
      · exact u32
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1544:ℝ)) (D := (448:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2581:ℝ)) (bi := (1472:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u41 : (2698:ℝ) ≤ x3 := by
    have hd : (y3-y1)^2 ≤ (1448:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact hy1L
      · exact u38
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x1)^2+(y3-y1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (698:ℝ)) (D := (1448:ℝ))
      (xi := x3) (xj := x1) (yi := y3) (yj := y1)
      (ai := (2581:ℝ)) (aj := (2000:ℝ)) (bj := (2302:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact u37) (by exact hx1L) (by norm_num)
    linarith only [hh]
  have u42 : y3 ≤ (1421:ℝ) := by
    have hd : (x3-x6)^2 ≤ (302:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u41
      · exact hx3U
      · exact u34
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1579:ℝ)) (D := (302:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2810:ℝ)) (bi := (1448:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3U) (by exact u33) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u43 : x4 ≤ (190:ℝ) := by
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
      (aj := (1258:ℝ)) (bi := (241:ℝ)) (bj := (1448:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact hx5L) (by exact u32) (by norm_num)
    linarith only [hh]
  have u44 : y4 ≤ (2302:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1448:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u43
      · exact hx5L
      · exact u32
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (698:ℝ)) (D := (1448:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2581:ℝ)) (bi := (2419:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u45 : (2698:ℝ) ≤ y5 := by
    have hd : (x5-x4)^2 ≤ (1448:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact u32
      · exact hx4L
      · exact u43
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y4)^2+(x5-x4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (698:ℝ)) (D := (1448:ℝ))
      (xi := y5) (xj := y4) (yi := x5) (yj := x4)
      (ai := (2581:ℝ)) (aj := (2000:ℝ)) (bj := (2302:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact u44) (by exact hy4L) (by norm_num)
    linarith only [hh]
  have u46 : x5 ≤ (1421:ℝ) := by
    have hd : (y5-y6)^2 ≤ (302:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u45
      · exact hy5U
      · exact u33
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1579:ℝ)) (D := (302:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2810:ℝ)) (bi := (1448:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u32) (by exact u34) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u47 : (2837:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (302:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u34
      · exact hx6U
      · exact u41
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1579:ℝ)) (D := (302:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2810:ℝ)) (aj := (1258:ℝ)) (bj := (1421:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u33) (by exact u42) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u48 : (2837:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (302:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u47
      · exact hy6U
      · exact u45
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1579:ℝ)) (D := (302:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2810:ℝ)) (aj := (1258:ℝ)) (bj := (1421:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u34) (by exact u46) (by exact hx5L) (by norm_num)
    linarith only [hh]
  have u49 : x0 ≤ (775:ℝ) := by
    have hd : (y0-y2)^2 ≤ (1456:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact u36
      · exact hy2L
      · exact u40
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (681:ℝ)) (D := (1456:ℝ))
      (xi := x0) (xj := x2) (yi := y0) (yj := y2)
      (aj := (1000:ℝ)) (bi := (826:ℝ)) (bj := (1456:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u35) (by exact hx2L) (by exact u39) (by norm_num)
    linarith only [hh]
  have u50 : y0 ≤ (775:ℝ) := by
    have hd : (x0-x2)^2 ≤ (1456:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u49
      · exact hx2L
      · exact u39
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y2)^2+(x0-x2)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (681:ℝ)) (D := (1456:ℝ))
      (xi := y0) (xj := y2) (yi := x0) (yj := x2)
      (aj := (1000:ℝ)) (bi := (826:ℝ)) (bj := (1456:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u36) (by exact hy2L) (by exact u40) (by norm_num)
    linarith only [hh]
  have u51 : x1 ≤ (2249:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1421:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u38
      · exact hy3L
      · exact u42
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (751:ℝ)) (D := (1421:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2698:ℝ)) (bi := (2302:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u37) (by exact u41) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u52 : y1 ≤ (163:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact u51
      · exact u41
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (190:ℝ)) (bj := (1421:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u38) (by exact hy3L) (by exact u42) (by norm_num)
    linarith only [hh]
  have u53 : (1012:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (1249:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u39
      · exact hx1L
      · exact u51
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1012:ℝ)) (D := (1249:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (163:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2L) (by exact u52) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u54 : x2 ≤ (1446:ℝ) := by
    have hd : (y2-y3)^2 ≤ (409:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u53
      · exact u40
      · exact hy3L
      · exact u42
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1554:ℝ)) (D := (409:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2698:ℝ)) (bi := (1456:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u39) (by exact u41) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u55 : y2 ≤ (1449:ℝ) := by
    have hd : (x2-x5)^2 ≤ (421:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u54
      · exact hx5L
      · exact u46
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1551:ℝ)) (D := (421:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2698:ℝ)) (bi := (1456:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u40) (by exact u45) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u56 : (2751:ℝ) ≤ x3 := by
    have hd : (y3-y1)^2 ≤ (1421:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact u42
      · exact hy1L
      · exact u52
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x1)^2+(y3-y1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (751:ℝ)) (D := (1421:ℝ))
      (xi := x3) (xj := x1) (yi := y3) (yj := y1)
      (ai := (2698:ℝ)) (aj := (2000:ℝ)) (bj := (2249:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u41) (by exact u51) (by exact hx1L) (by norm_num)
    linarith only [hh]
  have u57 : y3 ≤ (1412:ℝ) := by
    have hd : (x3-x6)^2 ≤ (249:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u56
      · exact hx3U
      · exact u48
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1588:ℝ)) (D := (249:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2837:ℝ)) (bi := (1421:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u42) (by exact u47) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u58 : x4 ≤ (163:ℝ) := by
    have hd : (y4-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact u44
      · exact u45
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1258:ℝ)) (bi := (190:ℝ)) (bj := (1421:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u43) (by exact hx5L) (by exact u46) (by norm_num)
    linarith only [hh]
  have u59 : y4 ≤ (2249:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1421:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u58
      · exact hx5L
      · exact u46
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (751:ℝ)) (D := (1421:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2698:ℝ)) (bi := (2302:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u44) (by exact u45) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u60 : (2751:ℝ) ≤ y5 := by
    have hd : (x5-x4)^2 ≤ (1421:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact u46
      · exact hx4L
      · exact u58
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y4)^2+(x5-x4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (751:ℝ)) (D := (1421:ℝ))
      (xi := y5) (xj := y4) (yi := x5) (yj := x4)
      (ai := (2698:ℝ)) (aj := (2000:ℝ)) (bj := (2249:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u45) (by exact u59) (by exact hy4L) (by norm_num)
    linarith only [hh]
  have u61 : x5 ≤ (1412:ℝ) := by
    have hd : (y5-y6)^2 ≤ (249:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u60
      · exact hy5U
      · exact u47
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1588:ℝ)) (D := (249:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2837:ℝ)) (bi := (1421:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u46) (by exact u48) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u62 : (2846:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (249:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u48
      · exact hx6U
      · exact u56
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1588:ℝ)) (D := (249:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2837:ℝ)) (aj := (1258:ℝ)) (bj := (1412:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u47) (by exact u57) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u63 : (2846:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (249:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u62
      · exact hy6U
      · exact u60
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1588:ℝ)) (D := (249:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2837:ℝ)) (aj := (1258:ℝ)) (bj := (1412:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u48) (by exact u61) (by exact hx5L) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u49, hy0L, u50, hx1L, u51, hy1L, u52, hx2L, u54, u53, u55, u56, hx3U, hy3L, u57, hx4L, u58, hy4L, u59, hx5L, u61, u60, hy5U, u63, hx6U, u62, hy6U⟩
