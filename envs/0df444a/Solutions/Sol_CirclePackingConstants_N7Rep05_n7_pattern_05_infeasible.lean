-- Prove2me | solution 1 for CirclePackingConstants.N7Rep05.n7_pattern_05_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T00:18:02.015281+00:00
-- url     : https://prove2.me/submissions/33a4795a-e692-4cc1-b2d4-06d4e52275fa

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
noncomputable section
namespace CirclePackingConstants
namespace N7Rep05

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
lemma n7_stage_0 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L : (1000:ℝ) ≤ x0) (hx0U : x0 ≤ (2000:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (1000:ℝ))
  (hx1L : (2000:ℝ) ≤ x1) (hx1U : x1 ≤ (3000:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (1000:ℝ))
  (hx2L : (0:ℝ) ≤ x2) (hx2U : x2 ≤ (1000:ℝ)) (hy2L : (1000:ℝ) ≤ y2) (hy2U : y2 ≤ (2000:ℝ))
  (hx3L : (1000:ℝ) ≤ x3) (hx3U : x3 ≤ (2000:ℝ)) (hy3L : (1000:ℝ) ≤ y3) (hy3U : y3 ≤ (2000:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (1000:ℝ)) (hy4L : (2000:ℝ) ≤ y4) (hy4U : y4 ≤ (3000:ℝ))
  (hx5L : (1000:ℝ) ≤ x5) (hx5U : x5 ≤ (2000:ℝ)) (hy5L : (2000:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2000:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2000:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (1000:ℝ) ≤ x0 ∧ x0 ≤ (1419:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (241:ℝ) ∧ (2258:ℝ) ≤ x1 ∧ x1 ≤ (3000:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (993:ℝ) ∧ (0:ℝ) ≤ x2 ∧ x2 ≤ (472:ℝ) ∧ (1000:ℝ) ≤ y2 ∧ y2 ≤ (1464:ℝ) ∧ (1581:ℝ) ≤ x3 ∧ x3 ≤ (2000:ℝ) ∧ (1258:ℝ) ≤ y3 ∧ y3 ≤ (1472:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (241:ℝ) ∧ (2426:ℝ) ≤ y4 ∧ y4 ≤ (3000:ℝ) ∧ (1501:ℝ) ≤ x5 ∧ x5 ≤ (1742:ℝ) ∧ (2759:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2759:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2000:ℝ) ≤ y6 ∧ y6 ≤ (2419:ℝ) := by
  have u0 : x0 ≤ (1742:ℝ) := by
    have hd : (y0-y1)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact hy0U
      · exact hy1L
      · exact hy1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x1)^2+(y0-y1)^2 := by nlinarith only [hT01]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x0) (xj := x1) (yi := y0) (yj := y1)
      (aj := (2000:ℝ)) (bi := (2000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx0U) (by exact hx1L) (by exact hx1U) (by norm_num)
    linarith only [hh]
  have u1 : y0 ≤ (742:ℝ) := by
    have hd : (x0-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u0
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y3)^2+(x0-x3)^2 := by nlinarith only [hT03]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y0) (xj := y3) (yi := x0) (yj := x3)
      (aj := (1000:ℝ)) (bi := (1000:ℝ)) (bj := (2000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy0U) (by exact hy3L) (by exact hy3U) (by norm_num)
    linarith only [hh]
  have u2 : (2258:ℝ) ≤ x1 := by
    have hd : (y1-y0)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact hy0L
      · exact u1
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x0)^2+(y1-y0)^2 := by nlinarith only [hT01]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x1) (xj := x0) (yi := y1) (yj := y0)
      (ai := (2000:ℝ)) (aj := (1000:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1L) (by exact u0) (by exact hx0L) (by norm_num)
    linarith only [hh]
  have u3 : x2 ≤ (742:ℝ) := by
    have hd : (y2-y3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy2L
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (1000:ℝ)) (bi := (1000:ℝ)) (bj := (2000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u4 : y2 ≤ (1742:ℝ) := by
    have hd : (x2-x4)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u3
      · exact hx4L
      · exact hx4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y4)^2+(x2-x4)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y2) (xj := y4) (yi := x2) (yj := x4)
      (aj := (2000:ℝ)) (bi := (2000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact hy4L) (by exact hy4U) (by norm_num)
    linarith only [hh]
  have u5 : (1258:ℝ) ≤ y3 := by
    have hd : (x3-x0)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx3L
      · exact hx3U
      · exact hx0L
      · exact u0
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y0)^2+(x3-x0)^2 := by nlinarith only [hT03]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y3) (xj := y0) (yi := x3) (yj := x0)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact u1) (by exact hy0L) (by norm_num)
    linarith only [hh]
  have u6 : (1258:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u5
      · exact hy3U
      · exact hy2L
      · exact u4
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact u3) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have u7 : y3 ≤ (1742:ℝ) := by
    have hd : (x3-x5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u6
      · exact hx3U
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y5)^2+(x3-x5)^2 := by nlinarith only [hT35]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y3) (xj := y5) (yi := x3) (yj := x5)
      (aj := (2000:ℝ)) (bi := (2000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u8 : (2258:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact hx4U
      · exact hx2L
      · exact u3
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2000:ℝ)) (aj := (1000:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4L) (by exact u4) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u9 : x4 ≤ (742:ℝ) := by
    have hd : (y4-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u8
      · exact hy4U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1000:ℝ)) (bi := (1000:ℝ)) (bj := (2000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
    linarith only [hh]
  have u10 : (2516:ℝ) ≤ y5 := by
    have hd : (x5-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact u6
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y3)^2+(x5-x3)^2 := by nlinarith only [hT35]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y5) (xj := y3) (yi := x5) (yj := x3)
      (ai := (2000:ℝ)) (aj := (1258:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact u7) (by exact u5) (by norm_num)
    linarith only [hh]
  have u11 : (1426:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u10
      · exact hy5U
      · exact u8
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5L) (by exact u9) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u12 : x5 ≤ (1742:ℝ) := by
    have hd : (y5-y6)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u10
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2000:ℝ)) (bi := (2000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u13 : (2684:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy6L
      · exact hy6U
      · exact u10
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2000:ℝ)) (aj := (1426:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u12) (by exact u11) (by norm_num)
    linarith only [hh]
  have u14 : y0 ≤ (484:ℝ) := by
    have hd : (x0-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u0
      · exact u6
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y3)^2+(x0-x3)^2 := by nlinarith only [hT03]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y0) (xj := y3) (yi := x0) (yj := x3)
      (aj := (1258:ℝ)) (bi := (742:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u1) (by exact u5) (by exact u7) (by norm_num)
    linarith only [hh]
  have u15 : x2 ≤ (574:ℝ) := by
    have hd : (y2-y3)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy2L
      · exact u4
      · exact u5
      · exact u7
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (1258:ℝ)) (bi := (742:ℝ)) (bj := (2000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u3) (by exact u6) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u16 : y2 ≤ (1574:ℝ) := by
    have hd : (x2-x4)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u15
      · exact hx4L
      · exact u9
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y4)^2+(x2-x4)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := y2) (xj := y4) (yi := x2) (yj := x4)
      (aj := (2258:ℝ)) (bi := (1742:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u4) (by exact u8) (by exact hy4U) (by norm_num)
    linarith only [hh]
  have u17 : (1426:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u5
      · exact u7
      · exact hy2L
      · exact u16
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (1258:ℝ)) (aj := (0:ℝ)) (bj := (574:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u6) (by exact u15) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have u18 : y3 ≤ (1499:ℝ) := by
    have hd : (x3-x5)^2 ≤ (574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u17
      · exact hx3U
      · exact u11
      · exact u12
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y5)^2+(x3-x5)^2 := by nlinarith only [hT35]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1501:ℝ)) (D := (574:ℝ))
      (xi := y3) (xj := y5) (yi := x3) (yj := x5)
      (aj := (2516:ℝ)) (bi := (1742:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u7) (by exact u10) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u19 : (2426:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u9
      · exact hx2L
      · exact u15
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2258:ℝ)) (aj := (1000:ℝ)) (bj := (1574:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u8) (by exact u16) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u20 : x4 ≤ (241:ℝ) := by
    have hd : (y4-y5)^2 ≤ (574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u19
      · exact hy4U
      · exact u10
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1501:ℝ)) (D := (574:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1426:ℝ)) (bi := (742:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u9) (by exact u11) (by exact u12) (by norm_num)
    linarith only [hh]
  have u21 : (2759:ℝ) ≤ y5 := by
    have hd : (x5-x3)^2 ≤ (574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u11
      · exact u12
      · exact u17
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y3)^2+(x5-x3)^2 := by nlinarith only [hT35]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1501:ℝ)) (D := (574:ℝ))
      (xi := y5) (xj := y3) (yi := x5) (yj := x3)
      (ai := (2516:ℝ)) (aj := (1258:ℝ)) (bj := (1499:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u10) (by exact u18) (by exact u5) (by norm_num)
    linarith only [hh]
  have u22 : (1501:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u21
      · exact hy5U
      · exact u19
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1501:ℝ)) (D := (574:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1426:ℝ)) (aj := (0:ℝ)) (bj := (241:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u11) (by exact u20) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u23 : (2759:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy6L
      · exact hy6U
      · exact u21
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2684:ℝ)) (aj := (1501:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u13) (by exact u12) (by exact u22) (by norm_num)
    linarith only [hh]
  have u24 : y6 ≤ (2419:ℝ) := by
    have hd : (x6-x5)^2 ≤ (1499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u23
      · exact hx6U
      · exact u22
      · exact u12
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y5)^2+(x6-x5)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (581:ℝ)) (D := (1499:ℝ))
      (xi := y6) (xj := y5) (yi := x6) (yj := x5)
      (aj := (2759:ℝ)) (bi := (3000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6U) (by exact u21) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u25 : x0 ≤ (1419:ℝ) := by
    have hd : (y0-y3)^2 ≤ (1499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact u14
      · exact u5
      · exact u18
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x3)^2+(y0-y3)^2 := by nlinarith only [hT03]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (581:ℝ)) (D := (1499:ℝ))
      (xi := x0) (xj := x3) (yi := y0) (yj := y3)
      (aj := (1426:ℝ)) (bi := (1742:ℝ)) (bj := (2000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u0) (by exact u17) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u26 : y0 ≤ (241:ℝ) := by
    have hd : (x0-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u25
      · exact u17
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y3)^2+(x0-x3)^2 := by nlinarith only [hT03]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y0) (xj := y3) (yi := x0) (yj := x3)
      (aj := (1258:ℝ)) (bi := (484:ℝ)) (bj := (1499:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u14) (by exact u5) (by exact u18) (by norm_num)
    linarith only [hh]
  have u27 : y1 ≤ (993:ℝ) := by
    have hd : (x1-x6)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u2
      · exact hx1U
      · exact u23
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y6)^2+(x1-x6)^2 := by nlinarith only [hT16]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := y1) (xj := y6) (yi := x1) (yj := x6)
      (aj := (2000:ℝ)) (bi := (1000:ℝ)) (bj := (2419:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy6L) (by exact u24) (by norm_num)
    linarith only [hh]
  have u28 : x2 ≤ (472:ℝ) := by
    have hd : (y2-y3)^2 ≤ (499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy2L
      · exact u16
      · exact u5
      · exact u18
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1528:ℝ)) (D := (499:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (1426:ℝ)) (bi := (574:ℝ)) (bj := (2000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u15) (by exact u17) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u29 : y2 ≤ (1464:ℝ) := by
    have hd : (x2-x4)^2 ≤ (472:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u28
      · exact hx4L
      · exact u20
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y4)^2+(x2-x4)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1536:ℝ)) (D := (472:ℝ))
      (xi := y2) (xj := y4) (yi := x2) (yj := x4)
      (aj := (2426:ℝ)) (bi := (1574:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u16) (by exact u19) (by exact hy4U) (by norm_num)
    linarith only [hh]
  have u30 : (1581:ℝ) ≤ x3 := by
    have hd : (y3-y0)^2 ≤ (1499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u5
      · exact u18
      · exact hy0L
      · exact u26
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x0)^2+(y3-y0)^2 := by nlinarith only [hT03]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (581:ℝ)) (D := (1499:ℝ))
      (xi := x3) (xj := x0) (yi := y3) (yj := y0)
      (ai := (1426:ℝ)) (aj := (1000:ℝ)) (bj := (1419:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u17) (by exact u25) (by exact hx0L) (by norm_num)
    linarith only [hh]
  have u31 : y3 ≤ (1472:ℝ) := by
    have hd : (x3-x5)^2 ≤ (499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u30
      · exact hx3U
      · exact u22
      · exact u12
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y5)^2+(x3-x5)^2 := by nlinarith only [hT35]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1528:ℝ)) (D := (499:ℝ))
      (xi := y3) (xj := y5) (yi := x3) (yj := x5)
      (aj := (2759:ℝ)) (bi := (1499:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u18) (by exact u21) (by exact hy5U) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u25, hy0L, u26, u2, hx1U, hy1L, u27, hx2L, u28, hy2L, u29, u30, hx3U, u5, u31, hx4L, u20, u19, hy4U, u22, u12, u21, hy5U, u23, hx6U, hy6L, u24⟩
lemma n7_stage_1 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L : (1000:ℝ) ≤ x0) (hx0U : x0 ≤ (1419:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (241:ℝ))
  (hx1L : (2258:ℝ) ≤ x1) (hx1U : x1 ≤ (3000:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (993:ℝ))
  (hx2L : (0:ℝ) ≤ x2) (hx2U : x2 ≤ (472:ℝ)) (hy2L : (1000:ℝ) ≤ y2) (hy2U : y2 ≤ (1464:ℝ))
  (hx3L : (1581:ℝ) ≤ x3) (hx3U : x3 ≤ (2000:ℝ)) (hy3L : (1258:ℝ) ≤ y3) (hy3U : y3 ≤ (1472:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (241:ℝ)) (hy4L : (2426:ℝ) ≤ y4) (hy4U : y4 ≤ (3000:ℝ))
  (hx5L : (1501:ℝ) ≤ x5) (hx5U : x5 ≤ (1742:ℝ)) (hy5L : (2759:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2759:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2000:ℝ) ≤ y6) (hy6U : y6 ≤ (2419:ℝ))
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
  : (1000:ℝ) ≤ x0 ∧ x0 ≤ (1002:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (1:ℝ) ∧ (2438:ℝ) ≤ x1 ∧ x1 ≤ (3000:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (565:ℝ) ∧ (0:ℝ) ≤ x2 ∧ x2 ≤ (346:ℝ) ∧ (1020:ℝ) ≤ y2 ∧ y2 ≤ (1430:ℝ) ∧ (1646:ℝ) ≤ x3 ∧ x3 ≤ (1734:ℝ) ∧ (1340:ℝ) ≤ y3 ∧ y3 ≤ (1431:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (188:ℝ) ∧ (2590:ℝ) ≤ y4 ∧ y4 ≤ (3000:ℝ) ∧ (1554:ℝ) ≤ x5 ∧ x5 ≤ (1731:ℝ) ∧ (2935:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2951:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2206:ℝ) ≤ y6 ∧ y6 ≤ (2298:ℝ) := by
  have u32 : x3 ≤ (1888:ℝ) := by
    have hd : (y3-y6)^2 ≤ (1161:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x6)^2+(y3-y6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1112:ℝ)) (D := (1161:ℝ))
      (xi := x3) (xj := x6) (yi := y3) (yj := y6)
      (aj := (2759:ℝ)) (bi := (2000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u33 : (2536:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (472:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact hx4U
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1536:ℝ)) (D := (472:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2426:ℝ)) (aj := (1000:ℝ)) (bj := (1464:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4L) (by exact hy2U) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u34 : x4 ≤ (203:ℝ) := by
    have hd : (y4-y5)^2 ≤ (464:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u33
      · exact hy4U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1539:ℝ)) (D := (464:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1501:ℝ)) (bi := (241:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
    linarith only [hh]
  have u35 : (2818:ℝ) ≤ y5 := by
    have hd : (x5-x3)^2 ≤ (387:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact hx3L
      · exact u32
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y3)^2+(x5-x3)^2 := by nlinarith only [hT35]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1560:ℝ)) (D := (387:ℝ))
      (xi := y5) (xj := y3) (yi := x5) (yj := x3)
      (ai := (2759:ℝ)) (aj := (1258:ℝ)) (bj := (1472:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact hy3U) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u36 : (1539:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (464:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u35
      · exact hy5U
      · exact u33
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1539:ℝ)) (D := (464:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1501:ℝ)) (aj := (0:ℝ)) (bj := (203:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5L) (by exact u34) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u37 : (2013:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (1419:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact hx3L
      · exact u32
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (755:ℝ)) (D := (1419:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2000:ℝ)) (aj := (1258:ℝ)) (bj := (1472:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact hy3U) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u38 : (2808:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (987:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u37
      · exact hy6U
      · exact u35
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1269:ℝ)) (D := (987:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2759:ℝ)) (aj := (1539:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact hx5U) (by exact u36) (by norm_num)
    linarith only [hh]
  have u39 : y6 ≤ (2330:ℝ) := by
    have hd : (x6-x5)^2 ≤ (1461:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u38
      · exact hx6U
      · exact u36
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y5)^2+(x6-x5)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (670:ℝ)) (D := (1461:ℝ))
      (xi := y6) (xj := y5) (yi := x6) (yj := x5)
      (aj := (2818:ℝ)) (bi := (2419:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6U) (by exact u35) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u40 : x0 ≤ (1242:ℝ) := by
    have hd : (y0-y3)^2 ≤ (1472:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact hy0U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x3)^2+(y0-y3)^2 := by nlinarith only [hT03]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (646:ℝ)) (D := (1472:ℝ))
      (xi := x0) (xj := x3) (yi := y0) (yj := y3)
      (aj := (1581:ℝ)) (bi := (1419:ℝ)) (bj := (1888:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx0U) (by exact hx3L) (by exact u32) (by norm_num)
    linarith only [hh]
  have u41 : y0 ≤ (132:ℝ) := by
    have hd : (x0-x3)^2 ≤ (888:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u40
      · exact hx3L
      · exact u32
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y3)^2+(x0-x3)^2 := by nlinarith only [hT03]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1340:ℝ)) (D := (888:ℝ))
      (xi := y0) (xj := y3) (yi := x0) (yj := x3)
      (aj := (1258:ℝ)) (bi := (241:ℝ)) (bj := (1472:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy0U) (by exact hy3L) (by exact hy3U) (by norm_num)
    linarith only [hh]
  have u42 : (2264:ℝ) ≤ x1 := by
    have hd : (y1-y0)^2 ≤ (993:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact hy0L
      · exact u41
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x0)^2+(y1-y0)^2 := by nlinarith only [hT01]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1264:ℝ)) (D := (993:ℝ))
      (xi := x1) (xj := x0) (yi := y1) (yj := y0)
      (ai := (2258:ℝ)) (aj := (1000:ℝ)) (bj := (1242:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1L) (by exact u40) (by exact hx0L) (by norm_num)
    linarith only [hh]
  have u43 : y1 ≤ (717:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1419:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u42
      · exact hx1U
      · exact hx3L
      · exact u32
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (755:ℝ)) (D := (1419:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (993:ℝ)) (bj := (1472:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy3L) (by exact hy3U) (by norm_num)
    linarith only [hh]
  have u44 : (1020:ℝ) ≤ y2 := by
    have hd : (x2-x0)^2 ≤ (1242:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact hx2U
      · exact hx0L
      · exact u40
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y0)^2+(x2-x0)^2 := by nlinarith only [hT02]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1020:ℝ)) (D := (1242:ℝ))
      (xi := y2) (xj := y0) (yi := x2) (yj := x0)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (132:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2L) (by exact u41) (by exact hy0L) (by norm_num)
    linarith only [hh]
  have u45 : x2 ≤ (346:ℝ) := by
    have hd : (y2-y3)^2 ≤ (452:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u44
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1542:ℝ)) (D := (452:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (1581:ℝ)) (bi := (472:ℝ)) (bj := (1888:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2U) (by exact hx3L) (by exact u32) (by norm_num)
    linarith only [hh]
  have u46 : y2 ≤ (1430:ℝ) := by
    have hd : (x2-x4)^2 ≤ (346:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u45
      · exact hx4L
      · exact u34
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y4)^2+(x2-x4)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1570:ℝ)) (D := (346:ℝ))
      (xi := y2) (xj := y4) (yi := x2) (yj := x4)
      (aj := (2536:ℝ)) (bi := (1464:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact u33) (by exact hy4U) (by norm_num)
    linarith only [hh]
  have u47 : (1646:ℝ) ≤ x3 := by
    have hd : (y3-y0)^2 ≤ (1472:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact hy0L
      · exact u41
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x0)^2+(y3-y0)^2 := by nlinarith only [hT03]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (646:ℝ)) (D := (1472:ℝ))
      (xi := x3) (xj := x0) (yi := y3) (yj := y0)
      (ai := (1581:ℝ)) (aj := (1000:ℝ)) (bj := (1242:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact u40) (by exact hx0L) (by norm_num)
    linarith only [hh]
  have u48 : (1340:ℝ) ≤ y3 := by
    have hd : (x3-x0)^2 ≤ (888:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u47
      · exact u32
      · exact hx0L
      · exact u40
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y0)^2+(x3-x0)^2 := by nlinarith only [hT03]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1340:ℝ)) (D := (888:ℝ))
      (xi := y3) (xj := y0) (yi := x3) (yj := x0)
      (ai := (1258:ℝ)) (aj := (0:ℝ)) (bj := (132:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact u41) (by exact hy0L) (by norm_num)
    linarith only [hh]
  have u49 : y3 ≤ (1431:ℝ) := by
    have hd : (x3-x5)^2 ≤ (349:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u47
      · exact u32
      · exact u36
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y5)^2+(x3-x5)^2 := by nlinarith only [hT35]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1569:ℝ)) (D := (349:ℝ))
      (xi := y3) (xj := y5) (yi := x3) (yj := x5)
      (aj := (2818:ℝ)) (bi := (1472:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3U) (by exact u35) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u50 : x3 ≤ (1734:ℝ) := by
    have hd : (y3-y6)^2 ≤ (990:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u48
      · exact u49
      · exact u37
      · exact u39
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x6)^2+(y3-y6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1266:ℝ)) (D := (990:ℝ))
      (xi := x3) (xj := x6) (yi := y3) (yj := y6)
      (aj := (2808:ℝ)) (bi := (1888:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u32) (by exact u38) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u51 : (2590:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (346:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u34
      · exact hx2L
      · exact u45
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1570:ℝ)) (D := (346:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2536:ℝ)) (aj := (1020:ℝ)) (bj := (1430:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u33) (by exact u46) (by exact u44) (by norm_num)
    linarith only [hh]
  have u52 : x4 ≤ (188:ℝ) := by
    have hd : (y4-y5)^2 ≤ (410:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u51
      · exact hy4U
      · exact u35
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1554:ℝ)) (D := (410:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1539:ℝ)) (bi := (203:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u34) (by exact u36) (by exact hx5U) (by norm_num)
    linarith only [hh]
  have u53 : (2935:ℝ) ≤ y5 := by
    have hd : (x5-x3)^2 ≤ (195:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u36
      · exact hx5U
      · exact u47
      · exact u50
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y3)^2+(x5-x3)^2 := by nlinarith only [hT35]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1595:ℝ)) (D := (195:ℝ))
      (xi := y5) (xj := y3) (yi := x5) (yj := x3)
      (ai := (2818:ℝ)) (aj := (1340:ℝ)) (bj := (1431:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u35) (by exact u49) (by exact u48) (by norm_num)
    linarith only [hh]
  have u54 : (1554:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (410:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u53
      · exact hy5U
      · exact u51
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1554:ℝ)) (D := (410:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1539:ℝ)) (aj := (0:ℝ)) (bj := (188:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u36) (by exact u52) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u55 : x5 ≤ (1731:ℝ) := by
    have hd : (y5-y6)^2 ≤ (987:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u53
      · exact hy5U
      · exact u37
      · exact u39
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1269:ℝ)) (D := (987:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2808:ℝ)) (bi := (1742:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5U) (by exact u38) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u56 : (2912:ℝ) ≤ x6 := by
    have hd : (y6-y3)^2 ≤ (990:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u37
      · exact u39
      · exact u48
      · exact u49
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x3)^2+(y6-y3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1266:ℝ)) (D := (990:ℝ))
      (xi := x6) (xj := x3) (yi := y6) (yj := y3)
      (ai := (2808:ℝ)) (aj := (1646:ℝ)) (bj := (1734:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u38) (by exact u50) (by exact u47) (by norm_num)
    linarith only [hh]
  have u57 : (2206:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (1354:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u56
      · exact hx6U
      · exact u47
      · exact u50
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (866:ℝ)) (D := (1354:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2013:ℝ)) (aj := (1340:ℝ)) (bj := (1431:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u37) (by exact u49) (by exact u48) (by norm_num)
    linarith only [hh]
  have u58 : (2951:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (794:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u57
      · exact u39
      · exact u53
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1397:ℝ)) (D := (794:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2912:ℝ)) (aj := (1554:ℝ)) (bj := (1731:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u56) (by exact u55) (by exact u54) (by norm_num)
    linarith only [hh]
  have u59 : y6 ≤ (2298:ℝ) := by
    have hd : (x6-x5)^2 ≤ (1446:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u58
      · exact hx6U
      · exact u54
      · exact u55
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y5)^2+(x6-x5)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (702:ℝ)) (D := (1446:ℝ))
      (xi := y6) (xj := y5) (yi := x6) (yj := x5)
      (aj := (2935:ℝ)) (bi := (2330:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u39) (by exact u53) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u60 : x0 ≤ (1002:ℝ) := by
    have hd : (y0-y3)^2 ≤ (1431:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact u41
      · exact u48
      · exact u49
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x3)^2+(y0-y3)^2 := by nlinarith only [hT03]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (732:ℝ)) (D := (1431:ℝ))
      (xi := x0) (xj := x3) (yi := y0) (yj := y3)
      (aj := (1646:ℝ)) (bi := (1242:ℝ)) (bj := (1734:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u40) (by exact u47) (by exact u50) (by norm_num)
    linarith only [hh]
  have u61 : y0 ≤ (1:ℝ) := by
    have hd : (x0-x3)^2 ≤ (734:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u60
      · exact u47
      · exact u50
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y3)^2+(x0-x3)^2 := by nlinarith only [hT03]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1430:ℝ)) (D := (734:ℝ))
      (xi := y0) (xj := y3) (yi := x0) (yj := x3)
      (aj := (1340:ℝ)) (bi := (132:ℝ)) (bj := (1431:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u41) (by exact u48) (by exact u49) (by norm_num)
    linarith only [hh]
  have u62 : (2438:ℝ) ≤ x1 := by
    have hd : (y1-y0)^2 ≤ (717:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u43
      · exact hy0L
      · exact u61
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x0)^2+(y1-y0)^2 := by nlinarith only [hT01]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1438:ℝ)) (D := (717:ℝ))
      (xi := x1) (xj := x0) (yi := y1) (yj := y0)
      (ai := (2264:ℝ)) (aj := (1000:ℝ)) (bj := (1002:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u42) (by exact u60) (by exact hx0L) (by norm_num)
    linarith only [hh]
  have u63 : y1 ≤ (565:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1354:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u62
      · exact hx1U
      · exact u47
      · exact u50
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (866:ℝ)) (D := (1354:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1340:ℝ)) (bi := (717:ℝ)) (bj := (1431:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u43) (by exact u48) (by exact u49) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u60, hy0L, u61, u62, hx1U, hy1L, u63, hx2L, u45, u44, u46, u47, u50, u48, u49, hx4L, u52, u51, hy4U, u54, u55, u53, hy5U, u58, hx6U, u57, u59⟩
lemma n7_stage_2 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L : (1000:ℝ) ≤ x0) (hx0U : x0 ≤ (1002:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (1:ℝ))
  (hx1L : (2438:ℝ) ≤ x1) (hx1U : x1 ≤ (3000:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (565:ℝ))
  (hx2L : (0:ℝ) ≤ x2) (hx2U : x2 ≤ (346:ℝ)) (hy2L : (1020:ℝ) ≤ y2) (hy2U : y2 ≤ (1430:ℝ))
  (hx3L : (1646:ℝ) ≤ x3) (hx3U : x3 ≤ (1734:ℝ)) (hy3L : (1340:ℝ) ≤ y3) (hy3U : y3 ≤ (1431:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (188:ℝ)) (hy4L : (2590:ℝ) ≤ y4) (hy4U : y4 ≤ (3000:ℝ))
  (hx5L : (1554:ℝ) ≤ x5) (hx5U : x5 ≤ (1731:ℝ)) (hy5L : (2935:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2951:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2206:ℝ) ≤ y6) (hy6U : y6 ≤ (2298:ℝ))
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
  : (1000:ℝ) ≤ x0 ∧ x0 ≤ (1002:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (1:ℝ) ∧ (2438:ℝ) ≤ x1 ∧ x1 ≤ (3000:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (565:ℝ) ∧ (0:ℝ) ≤ x2 ∧ x2 ≤ (136:ℝ) ∧ (1257:ℝ) ≤ y2 ∧ y2 ≤ (1404:ℝ) ∧ (1732:ℝ) ≤ x3 ∧ x3 ≤ (1734:ℝ) ∧ (1430:ℝ) ≤ y3 ∧ y3 ≤ (1431:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (131:ℝ) ∧ (2853:ℝ) ≤ y4 ∧ y4 ≤ (3000:ℝ) ∧ (1554:ℝ) ≤ x5 ∧ x5 ≤ (1731:ℝ) ∧ (2935:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2951:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2206:ℝ) ≤ y6 ∧ y6 ≤ (2298:ℝ) := by
  have u64 : x2 ≤ (268:ℝ) := by
    have hd : (y2-y0)^2 ≤ (1430:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy2L
      · exact hy2U
      · exact hy0L
      · exact hy0U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x0)^2+(y2-y0)^2 := by nlinarith only [hT02]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (734:ℝ)) (D := (1430:ℝ))
      (xi := x2) (xj := x0) (yi := y2) (yj := y0)
      (aj := (1000:ℝ)) (bi := (346:ℝ)) (bj := (1002:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2U) (by exact hx0L) (by exact hx0U) (by norm_num)
    linarith only [hh]
  have u65 : (1257:ℝ) ≤ y2 := by
    have hd : (x2-x0)^2 ≤ (1002:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u64
      · exact hx0L
      · exact hx0U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y0)^2+(x2-x0)^2 := by nlinarith only [hT02]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1257:ℝ)) (D := (1002:ℝ))
      (xi := y2) (xj := y0) (yi := x2) (yj := x0)
      (ai := (1020:ℝ)) (aj := (0:ℝ)) (bj := (1:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2L) (by exact hy0U) (by exact hy0L) (by norm_num)
    linarith only [hh]
  have u66 : x2 ≤ (136:ℝ) := by
    have hd : (y2-y3)^2 ≤ (174:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u65
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1598:ℝ)) (D := (174:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (1646:ℝ)) (bi := (268:ℝ)) (bj := (1734:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u64) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u67 : y2 ≤ (1404:ℝ) := by
    have hd : (x2-x4)^2 ≤ (188:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u66
      · exact hx4L
      · exact hx4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y4)^2+(x2-x4)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1596:ℝ)) (D := (188:ℝ))
      (xi := y2) (xj := y4) (yi := x2) (yj := x4)
      (aj := (2590:ℝ)) (bi := (1430:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact hy4L) (by exact hy4U) (by norm_num)
    linarith only [hh]
  have u68 : (1732:ℝ) ≤ x3 := by
    have hd : (y3-y0)^2 ≤ (1431:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact hy0L
      · exact hy0U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x0)^2+(y3-y0)^2 := by nlinarith only [hT03]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (732:ℝ)) (D := (1431:ℝ))
      (xi := x3) (xj := x0) (yi := y3) (yj := y0)
      (ai := (1646:ℝ)) (aj := (1000:ℝ)) (bj := (1002:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact hx0U) (by exact hx0L) (by norm_num)
    linarith only [hh]
  have u69 : (1430:ℝ) ≤ y3 := by
    have hd : (x3-x0)^2 ≤ (734:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u68
      · exact hx3U
      · exact hx0L
      · exact hx0U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y0)^2+(x3-x0)^2 := by nlinarith only [hT03]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1430:ℝ)) (D := (734:ℝ))
      (xi := y3) (xj := y0) (yi := x3) (yj := x0)
      (ai := (1340:ℝ)) (aj := (0:ℝ)) (bj := (1:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact hy0U) (by exact hy0L) (by norm_num)
    linarith only [hh]
  have u70 : (2853:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (188:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact hx4U
      · exact hx2L
      · exact u66
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1596:ℝ)) (D := (188:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2590:ℝ)) (aj := (1257:ℝ)) (bj := (1404:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4L) (by exact u67) (by exact u65) (by norm_num)
    linarith only [hh]
  have u71 : x4 ≤ (131:ℝ) := by
    have hd : (y4-y5)^2 ≤ (147:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u70
      · exact hy4U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1600:ℝ)) (D := (147:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1554:ℝ)) (bi := (188:ℝ)) (bj := (1731:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, hx0U, hy0L, hy0U, hx1L, hx1U, hy1L, hy1U, hx2L, u66, u65, u67, u68, hx3U, u69, hy3U, hx4L, u71, u70, hy4U, hx5L, hx5U, hy5L, hy5U, hx6L, hx6U, hy6L, hy6U⟩
end N7Rep05
end CirclePackingConstants
open CirclePackingConstants.N7Rep05
lemma n7_rep05_terminal (x3 y3 x5 y5 : ℝ)
    (hx3L : (1732:ℝ) ≤ x3) (hx3U : x3 ≤ (1734:ℝ))
    (hy3L : (1430:ℝ) ≤ y3) (hy3U : y3 ≤ (1431:ℝ))
    (hx5L : (1554:ℝ) ≤ x5) (hx5U : x5 ≤ (1731:ℝ))
    (hy5L : (2935:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
    (hT35 : (2584683:ℝ) < (x3-x5)^2+(y3-y5)^2) : False := by
  have dX : (x3-x5)^2 ≤ (180:ℝ)^2 := by
    apply sqdiff_bound_contract
    · exact hx3L
    · exact hx3U
    · exact hx5L
    · exact hx5U
    · norm_num
    · norm_num
  have dY : (y3-y5)^2 ≤ (1570:ℝ)^2 := by
    apply sqdiff_bound_contract
    · exact hy3L
    · exact hy3U
    · exact hy5L
    · exact hy5U
    · norm_num
    · norm_num
  have hc : (180:ℝ)^2 + (1570:ℝ)^2 < (2584683:ℝ) := by norm_num
  linarith only [hT35, dX, dY, hc]
theorem solution (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L:(1000:ℝ)≤x0) (hx0U:x0≤(2000:ℝ)) (hy0L:(0:ℝ)≤y0) (hy0U:y0≤(1000:ℝ))
  (hx1L:(2000:ℝ)≤x1) (hx1U:x1≤(3000:ℝ)) (hy1L:(0:ℝ)≤y1) (hy1U:y1≤(1000:ℝ))
  (hx2L:(0:ℝ)≤x2) (hx2U:x2≤(1000:ℝ)) (hy2L:(1000:ℝ)≤y2) (hy2U:y2≤(2000:ℝ))
  (hx3L:(1000:ℝ)≤x3) (hx3U:x3≤(2000:ℝ)) (hy3L:(1000:ℝ)≤y3) (hy3U:y3≤(2000:ℝ))
  (hx4L:(0:ℝ)≤x4) (hx4U:x4≤(1000:ℝ)) (hy4L:(2000:ℝ)≤y4) (hy4U:y4≤(3000:ℝ))
  (hx5L:(1000:ℝ)≤x5) (hx5U:x5≤(2000:ℝ)) (hy5L:(2000:ℝ)≤y5) (hy5U:y5≤(3000:ℝ))
  (hx6L:(2000:ℝ)≤x6) (hx6U:x6≤(3000:ℝ)) (hy6L:(2000:ℝ)≤y6) (hy6U:y6≤(3000:ℝ))
  (hT01:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2)
  (hT02:(2584683:ℝ)<(x0-x2)^2+(y0-y2)^2)
  (hT03:(2584683:ℝ)<(x0-x3)^2+(y0-y3)^2)
  (hT04:(2584683:ℝ)<(x0-x4)^2+(y0-y4)^2)
  (hT05:(2584683:ℝ)<(x0-x5)^2+(y0-y5)^2)
  (hT06:(2584683:ℝ)<(x0-x6)^2+(y0-y6)^2)
  (hT12:(2584683:ℝ)<(x1-x2)^2+(y1-y2)^2)
  (hT13:(2584683:ℝ)<(x1-x3)^2+(y1-y3)^2)
  (hT14:(2584683:ℝ)<(x1-x4)^2+(y1-y4)^2)
  (hT15:(2584683:ℝ)<(x1-x5)^2+(y1-y5)^2)
  (hT16:(2584683:ℝ)<(x1-x6)^2+(y1-y6)^2)
  (hT23:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2)
  (hT24:(2584683:ℝ)<(x2-x4)^2+(y2-y4)^2)
  (hT25:(2584683:ℝ)<(x2-x5)^2+(y2-y5)^2)
  (hT26:(2584683:ℝ)<(x2-x6)^2+(y2-y6)^2)
  (hT34:(2584683:ℝ)<(x3-x4)^2+(y3-y4)^2)
  (hT35:(2584683:ℝ)<(x3-x5)^2+(y3-y5)^2)
  (hT36:(2584683:ℝ)<(x3-x6)^2+(y3-y6)^2)
  (hT45:(2584683:ℝ)<(x4-x5)^2+(y4-y5)^2)
  (hT46:(2584683:ℝ)<(x4-x6)^2+(y4-y6)^2)
  (hT56:(2584683:ℝ)<(x5-x6)^2+(y5-y6)^2)
  : False := by
  have q0 := n7_stage_0
    (x0 := x0)
    (y0 := y0)
    (x1 := x1)
    (y1 := y1)
    (x2 := x2)
    (y2 := y2)
    (x3 := x3)
    (y3 := y3)
    (x4 := x4)
    (y4 := y4)
    (x5 := x5)
    (y5 := y5)
    (x6 := x6)
    (y6 := y6)
    (hx0L := hx0L)
    (hx0U := hx0U)
    (hy0L := hy0L)
    (hy0U := hy0U)
    (hx1L := hx1L)
    (hx1U := hx1U)
    (hy1L := hy1L)
    (hy1U := hy1U)
    (hx2L := hx2L)
    (hx2U := hx2U)
    (hy2L := hy2L)
    (hy2U := hy2U)
    (hx3L := hx3L)
    (hx3U := hx3U)
    (hy3L := hy3L)
    (hy3U := hy3U)
    (hx4L := hx4L)
    (hx4U := hx4U)
    (hy4L := hy4L)
    (hy4U := hy4U)
    (hx5L := hx5L)
    (hx5U := hx5U)
    (hy5L := hy5L)
    (hy5U := hy5U)
    (hx6L := hx6L)
    (hx6U := hx6U)
    (hy6L := hy6L)
    (hy6U := hy6U)
    (hT01 := hT01)
    (hT02 := hT02)
    (hT03 := hT03)
    (hT04 := hT04)
    (hT05 := hT05)
    (hT06 := hT06)
    (hT12 := hT12)
    (hT13 := hT13)
    (hT14 := hT14)
    (hT15 := hT15)
    (hT16 := hT16)
    (hT23 := hT23)
    (hT24 := hT24)
    (hT25 := hT25)
    (hT26 := hT26)
    (hT34 := hT34)
    (hT35 := hT35)
    (hT36 := hT36)
    (hT45 := hT45)
    (hT46 := hT46)
    (hT56 := hT56)
  rcases q0 with ⟨s0x0L,s0x0U,s0x1L,s0x1U,s0x2L,s0x2U,s0x3L,s0x3U,s0x4L,s0x4U,s0x5L,s0x5U,s0x6L,s0x6U,s0y0L,s0y0U,s0y1L,s0y1U,s0y2L,s0y2U,s0y3L,s0y3U,s0y4L,s0y4U,s0y5L,s0y5U,s0y6L,s0y6U⟩
  have q1 := n7_stage_1
    (x0 := x0)
    (y0 := y0)
    (x1 := x1)
    (y1 := y1)
    (x2 := x2)
    (y2 := y2)
    (x3 := x3)
    (y3 := y3)
    (x4 := x4)
    (y4 := y4)
    (x5 := x5)
    (y5 := y5)
    (x6 := x6)
    (y6 := y6)
    (hx0L := s0x0L)
    (hx0U := s0x0U)
    (hy0L := s0x1L)
    (hy0U := s0x1U)
    (hx1L := s0x2L)
    (hx1U := s0x2U)
    (hy1L := s0x3L)
    (hy1U := s0x3U)
    (hx2L := s0x4L)
    (hx2U := s0x4U)
    (hy2L := s0x5L)
    (hy2U := s0x5U)
    (hx3L := s0x6L)
    (hx3U := s0x6U)
    (hy3L := s0y0L)
    (hy3U := s0y0U)
    (hx4L := s0y1L)
    (hx4U := s0y1U)
    (hy4L := s0y2L)
    (hy4U := s0y2U)
    (hx5L := s0y3L)
    (hx5U := s0y3U)
    (hy5L := s0y4L)
    (hy5U := s0y4U)
    (hx6L := s0y5L)
    (hx6U := s0y5U)
    (hy6L := s0y6L)
    (hy6U := s0y6U)
    (hT01 := hT01)
    (hT02 := hT02)
    (hT03 := hT03)
    (hT04 := hT04)
    (hT05 := hT05)
    (hT06 := hT06)
    (hT12 := hT12)
    (hT13 := hT13)
    (hT14 := hT14)
    (hT15 := hT15)
    (hT16 := hT16)
    (hT23 := hT23)
    (hT24 := hT24)
    (hT25 := hT25)
    (hT26 := hT26)
    (hT34 := hT34)
    (hT35 := hT35)
    (hT36 := hT36)
    (hT45 := hT45)
    (hT46 := hT46)
    (hT56 := hT56)
  rcases q1 with ⟨s1x0L,s1x0U,s1x1L,s1x1U,s1x2L,s1x2U,s1x3L,s1x3U,s1x4L,s1x4U,s1x5L,s1x5U,s1x6L,s1x6U,s1y0L,s1y0U,s1y1L,s1y1U,s1y2L,s1y2U,s1y3L,s1y3U,s1y4L,s1y4U,s1y5L,s1y5U,s1y6L,s1y6U⟩
  have q2 := n7_stage_2
    (x0 := x0)
    (y0 := y0)
    (x1 := x1)
    (y1 := y1)
    (x2 := x2)
    (y2 := y2)
    (x3 := x3)
    (y3 := y3)
    (x4 := x4)
    (y4 := y4)
    (x5 := x5)
    (y5 := y5)
    (x6 := x6)
    (y6 := y6)
    (hx0L := s1x0L)
    (hx0U := s1x0U)
    (hy0L := s1x1L)
    (hy0U := s1x1U)
    (hx1L := s1x2L)
    (hx1U := s1x2U)
    (hy1L := s1x3L)
    (hy1U := s1x3U)
    (hx2L := s1x4L)
    (hx2U := s1x4U)
    (hy2L := s1x5L)
    (hy2U := s1x5U)
    (hx3L := s1x6L)
    (hx3U := s1x6U)
    (hy3L := s1y0L)
    (hy3U := s1y0U)
    (hx4L := s1y1L)
    (hx4U := s1y1U)
    (hy4L := s1y2L)
    (hy4U := s1y2U)
    (hx5L := s1y3L)
    (hx5U := s1y3U)
    (hy5L := s1y4L)
    (hy5U := s1y4U)
    (hx6L := s1y5L)
    (hx6U := s1y5U)
    (hy6L := s1y6L)
    (hy6U := s1y6U)
    (hT01 := hT01)
    (hT02 := hT02)
    (hT03 := hT03)
    (hT04 := hT04)
    (hT05 := hT05)
    (hT06 := hT06)
    (hT12 := hT12)
    (hT13 := hT13)
    (hT14 := hT14)
    (hT15 := hT15)
    (hT16 := hT16)
    (hT23 := hT23)
    (hT24 := hT24)
    (hT25 := hT25)
    (hT26 := hT26)
    (hT34 := hT34)
    (hT35 := hT35)
    (hT36 := hT36)
    (hT45 := hT45)
    (hT46 := hT46)
    (hT56 := hT56)
  rcases q2 with ⟨s2x0L,s2x0U,s2x1L,s2x1U,s2x2L,s2x2U,s2x3L,s2x3U,s2x4L,s2x4U,s2x5L,s2x5U,s2x6L,s2x6U,s2y0L,s2y0U,s2y1L,s2y1U,s2y2L,s2y2U,s2y3L,s2y3U,s2y4L,s2y4U,s2y5L,s2y5U,s2y6L,s2y6U⟩
  exact n7_rep05_terminal (x3 := x3) (y3 := y3) (x5 := x5) (y5 := y5)
    (hx3L := s2x6L)
    (hx3U := s2x6U)
    (hy3L := s2y0L)
    (hy3U := s2y0U)
    (hx5L := s2y3L)
    (hx5U := s2y3U)
    (hy5L := s2y4L)
    (hy5U := s2y4U)
    (hT35 := hT35)
