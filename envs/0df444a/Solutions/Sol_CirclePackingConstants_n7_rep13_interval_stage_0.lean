-- Prove2me | solution 1 for CirclePackingConstants.n7_rep13_interval_stage_0
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:00:26.771973+00:00
-- url     : https://prove2.me/submissions/18dcd32a-f68c-4031-8f19-cd53971c996a

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
  (hx1L : (2000:ℝ) ≤ x1) (hx1U : x1 ≤ (3000:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (1000:ℝ))
  (hx2L : (1000:ℝ) ≤ x2) (hx2U : x2 ≤ (2000:ℝ)) (hy2L : (1000:ℝ) ≤ y2) (hy2U : y2 ≤ (2000:ℝ))
  (hx3L : (2000:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1000:ℝ) ≤ y3) (hy3U : y3 ≤ (2000:ℝ))
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
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (1000:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (1000:ℝ) ∧ (2000:ℝ) ≤ x1 ∧ x1 ≤ (2419:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (241:ℝ) ∧ (1000:ℝ) ≤ x2 ∧ x2 ≤ (1472:ℝ) ∧ (1000:ℝ) ≤ y2 ∧ y2 ≤ (1472:ℝ) ∧ (2581:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1258:ℝ) ≤ y3 ∧ y3 ≤ (1448:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (241:ℝ) ∧ (2000:ℝ) ≤ y4 ∧ y4 ≤ (2419:ℝ) ∧ (1258:ℝ) ≤ x5 ∧ x5 ≤ (1499:ℝ) ∧ (2581:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2759:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2759:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
  have u0 : y1 ≤ (742:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact hx1U
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1000:ℝ)) (bi := (1000:ℝ)) (bj := (2000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy3L) (by exact hy3U) (by norm_num)
    linarith only [hh]
  have u1 : x2 ≤ (1742:ℝ) := by
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
      (aj := (2000:ℝ)) (bi := (2000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u2 : y2 ≤ (1742:ℝ) := by
    have hd : (x2-x5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u1
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2000:ℝ)) (bi := (2000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u3 : (1258:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx3L
      · exact hx3U
      · exact hx1L
      · exact hx1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact u0) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u4 : (2258:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u3
      · exact hy3U
      · exact hy2L
      · exact u2
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2000:ℝ)) (aj := (1000:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact u1) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have u5 : y3 ≤ (1742:ℝ) := by
    have hd : (x3-x6)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u4
      · exact hx3U
      · exact hx6L
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2000:ℝ)) (bi := (2000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u6 : x4 ≤ (742:ℝ) := by
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
      (aj := (1000:ℝ)) (bi := (1000:ℝ)) (bj := (2000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
    linarith only [hh]
  have u7 : (2258:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact hx2L
      · exact u1
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2000:ℝ)) (aj := (1000:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact u2) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u8 : (1258:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u7
      · exact hy5U
      · exact hy4L
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5L) (by exact u6) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u9 : x5 ≤ (1742:ℝ) := by
    have hd : (y5-y6)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u7
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
  have u10 : (2516:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact u4
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2000:ℝ)) (aj := (1258:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact u5) (by exact u3) (by norm_num)
    linarith only [hh]
  have u11 : (2684:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u10
      · exact hy6U
      · exact u7
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2000:ℝ)) (aj := (1258:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u9) (by exact u8) (by norm_num)
    linarith only [hh]
  have u12 : y1 ≤ (484:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact hx1U
      · exact u4
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (742:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u0) (by exact u3) (by exact u5) (by norm_num)
    linarith only [hh]
  have u13 : x2 ≤ (1574:ℝ) := by
    have hd : (y2-y3)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy2L
      · exact u2
      · exact u3
      · exact u5
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2258:ℝ)) (bi := (1742:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u1) (by exact u4) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u14 : y2 ≤ (1574:ℝ) := by
    have hd : (x2-x5)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u13
      · exact u8
      · exact u9
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2258:ℝ)) (bi := (1742:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u2) (by exact u7) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u15 : (2426:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u3
      · exact u5
      · exact hy2L
      · exact u14
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2258:ℝ)) (aj := (1000:ℝ)) (bj := (1574:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u4) (by exact u13) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have u16 : y3 ≤ (1499:ℝ) := by
    have hd : (x3-x6)^2 ≤ (574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u15
      · exact hx3U
      · exact u11
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1501:ℝ)) (D := (574:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2516:ℝ)) (bi := (1742:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u5) (by exact u10) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u17 : x4 ≤ (484:ℝ) := by
    have hd : (y4-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact hy4U
      · exact u7
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1258:ℝ)) (bi := (742:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u6) (by exact u8) (by exact u9) (by norm_num)
    linarith only [hh]
  have u18 : (2426:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u8
      · exact u9
      · exact hx2L
      · exact u13
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2258:ℝ)) (aj := (1000:ℝ)) (bj := (1574:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u7) (by exact u14) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u19 : x5 ≤ (1499:ℝ) := by
    have hd : (y5-y6)^2 ≤ (574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u18
      · exact hy5U
      · exact u10
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1501:ℝ)) (D := (574:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2684:ℝ)) (bi := (1742:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u9) (by exact u11) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u20 : (2759:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u11
      · exact hx6U
      · exact u15
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1501:ℝ)) (D := (574:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2516:ℝ)) (aj := (1258:ℝ)) (bj := (1499:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u10) (by exact u16) (by exact u3) (by norm_num)
    linarith only [hh]
  have u21 : (2759:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u20
      · exact hy6U
      · exact u18
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1501:ℝ)) (D := (574:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2684:ℝ)) (aj := (1258:ℝ)) (bj := (1499:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u11) (by exact u19) (by exact u8) (by norm_num)
    linarith only [hh]
  have u22 : x1 ≤ (2419:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u12
      · exact u3
      · exact u16
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (581:ℝ)) (D := (1499:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2426:ℝ)) (bi := (3000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1U) (by exact u15) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u23 : y1 ≤ (241:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact u22
      · exact u15
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (484:ℝ)) (bj := (1499:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u12) (by exact u3) (by exact u16) (by norm_num)
    linarith only [hh]
  have u24 : x2 ≤ (1472:ℝ) := by
    have hd : (y2-y3)^2 ≤ (499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy2L
      · exact u14
      · exact u3
      · exact u16
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2 := by nlinarith only [hT23]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1528:ℝ)) (D := (499:ℝ))
      (xi := x2) (xj := x3) (yi := y2) (yj := y3)
      (aj := (2426:ℝ)) (bi := (1574:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u13) (by exact u15) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u25 : y2 ≤ (1472:ℝ) := by
    have hd : (x2-x5)^2 ≤ (499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u24
      · exact u8
      · exact u19
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y5)^2+(x2-x5)^2 := by nlinarith only [hT25]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1528:ℝ)) (D := (499:ℝ))
      (xi := y2) (xj := y5) (yi := x2) (yj := x5)
      (aj := (2426:ℝ)) (bi := (1574:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u14) (by exact u18) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u26 : (2581:ℝ) ≤ x3 := by
    have hd : (y3-y1)^2 ≤ (1499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u3
      · exact u16
      · exact hy1L
      · exact u23
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x1)^2+(y3-y1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (581:ℝ)) (D := (1499:ℝ))
      (xi := x3) (xj := x1) (yi := y3) (yj := y1)
      (ai := (2426:ℝ)) (aj := (2000:ℝ)) (bj := (2419:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u15) (by exact u22) (by exact hx1L) (by norm_num)
    linarith only [hh]
  have u27 : y3 ≤ (1448:ℝ) := by
    have hd : (x3-x6)^2 ≤ (419:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u26
      · exact hx3U
      · exact u21
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1552:ℝ)) (D := (419:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2759:ℝ)) (bi := (1499:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u16) (by exact u20) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u28 : x4 ≤ (241:ℝ) := by
    have hd : (y4-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact hy4U
      · exact u18
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1258:ℝ)) (bi := (484:ℝ)) (bj := (1499:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u17) (by exact u8) (by exact u19) (by norm_num)
    linarith only [hh]
  have u29 : y4 ≤ (2419:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u28
      · exact u8
      · exact u19
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (581:ℝ)) (D := (1499:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2426:ℝ)) (bi := (3000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4U) (by exact u18) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u30 : (2528:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u8
      · exact u19
      · exact hx2L
      · exact u24
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1528:ℝ)) (D := (499:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2426:ℝ)) (aj := (1000:ℝ)) (bj := (1472:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u18) (by exact u25) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u31 : (2581:ℝ) ≤ y5 := by
    have hd : (x5-x4)^2 ≤ (1499:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u8
      · exact u19
      · exact hx4L
      · exact u28
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y4)^2+(x5-x4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (581:ℝ)) (D := (1499:ℝ))
      (xi := y5) (xj := y4) (yi := x5) (yj := x4)
      (ai := (2528:ℝ)) (aj := (2000:ℝ)) (bj := (2419:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u30) (by exact u29) (by exact hy4L) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, hx0U, hy0L, hy0U, hx1L, u22, hy1L, u23, hx2L, u24, hy2L, u25, u26, hx3U, u3, u27, hx4L, u28, hy4L, u29, u8, u19, u31, hy5U, u21, hx6U, u20, hy6U⟩
