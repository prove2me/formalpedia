-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_04_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T00:14:21.871819+00:00
-- url     : https://prove2.me/submissions/dce45a46-1ca6-43c4-846f-e4951af02743

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
noncomputable section
namespace CirclePackingConstants
namespace N7Root

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
  : (1000:ℝ) ≤ x0 ∧ x0 ≤ (1742:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (1000:ℝ) ∧ (2258:ℝ) ≤ x1 ∧ x1 ≤ (3000:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (484:ℝ) ∧ (0:ℝ) ≤ x2 ∧ x2 ≤ (1000:ℝ) ∧ (1000:ℝ) ≤ y2 ∧ y2 ≤ (1742:ℝ) ∧ (2000:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1258:ℝ) ≤ y3 ∧ y3 ≤ (1742:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (484:ℝ) ∧ (2258:ℝ) ≤ y4 ∧ y4 ≤ (3000:ℝ) ∧ (1258:ℝ) ≤ x5 ∧ x5 ≤ (1742:ℝ) ∧ (2000:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2516:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2516:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
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
  have u1 : (2258:ℝ) ≤ x1 := by
    have hd : (y1-y0)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact hy0L
      · exact hy0U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x0)^2+(y1-y0)^2 := by nlinarith only [hT01]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x1) (xj := x0) (yi := y1) (yj := y0)
      (ai := (2000:ℝ)) (aj := (1000:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1L) (by exact u0) (by exact hx0L) (by norm_num)
    linarith only [hh]
  have u2 : y1 ≤ (742:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u1
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
  have u3 : y2 ≤ (1742:ℝ) := by
    have hd : (x2-x4)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact hx2U
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
  have u4 : (1258:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx3L
      · exact hx3U
      · exact u1
      · exact hx1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact u2) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u5 : y3 ≤ (1742:ℝ) := by
    have hd : (x3-x6)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx3L
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
  have u6 : (2258:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact hx4U
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2000:ℝ)) (aj := (1000:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4L) (by exact u3) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u7 : x4 ≤ (742:ℝ) := by
    have hd : (y4-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u6
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
  have u8 : (1258:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy5L
      · exact hy5U
      · exact u6
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1000:ℝ)) (aj := (0:ℝ)) (bj := (742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5L) (by exact u7) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u9 : x5 ≤ (1742:ℝ) := by
    have hd : (y5-y6)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy5L
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
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2000:ℝ)) (aj := (1258:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact u5) (by exact u4) (by norm_num)
    linarith only [hh]
  have u11 : (2516:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u10
      · exact hy6U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2000:ℝ)) (aj := (1258:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u9) (by exact u8) (by norm_num)
    linarith only [hh]
  have u12 : y1 ≤ (484:ℝ) := by
    have hd : (x1-x3)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u1
      · exact hx1U
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (742:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u2) (by exact u4) (by exact u5) (by norm_num)
    linarith only [hh]
  have u13 : x4 ≤ (484:ℝ) := by
    have hd : (y4-y5)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u6
      · exact hy4U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1258:ℝ)) (bi := (742:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u7) (by exact u8) (by exact u9) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u0, hy0L, hy0U, u1, hx1U, hy1L, u12, hx2L, hx2U, hy2L, u3, hx3L, hx3U, u4, u5, hx4L, u13, u6, hy4U, u8, u9, hy5L, hy5U, u11, hx6U, u10, hy6U⟩
end N7Root
end CirclePackingConstants
noncomputable section
namespace CirclePackingConstants
namespace N7LowCorrect

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
  (hx0L : (1000:ℝ) ≤ x0) (hx0U : x0 ≤ (1742:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (1000:ℝ))
  (hx1L : (2258:ℝ) ≤ x1) (hx1U : x1 ≤ (3000:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (484:ℝ))
  (hx2L : (0:ℝ) ≤ x2) (hx2U : x2 ≤ (1000:ℝ)) (hy2L : (1000:ℝ) ≤ y2) (hy2U : y2 ≤ (1742:ℝ))
  (hx3L : (2000:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1258:ℝ) ≤ y3) (hy3U : y3 ≤ (1742:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (484:ℝ)) (hy4L : (2258:ℝ) ≤ y4) (hy4U : y4 ≤ (3000:ℝ))
  (hx5L : (1258:ℝ) ≤ x5) (hx5U : x5 ≤ (1742:ℝ)) (hy5L : (2000:ℝ) ≤ y5) (hy5U : y5 ≤ (2500:ℝ))
  (hx6L : (2516:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2516:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (1000:ℝ) ≤ x0 ∧ x0 ≤ (1134:ℝ) ∧ (804:ℝ) ≤ y0 ∧ y0 ≤ (1000:ℝ) ∧ (2258:ℝ) ≤ x1 ∧ x1 ≤ (2392:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (62:ℝ) ∧ (0:ℝ) ≤ x2 ∧ x2 ≤ (1000:ℝ) ∧ (1000:ℝ) ≤ y2 ∧ y2 ≤ (1742:ℝ) ∧ (2866:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1426:ℝ) ≤ y3 ∧ y3 ≤ (1467:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (484:ℝ) ∧ (2258:ℝ) ≤ y4 ∧ y4 ≤ (3000:ℝ) ∧ (1258:ℝ) ≤ x5 ∧ x5 ≤ (1742:ℝ) ∧ (2000:ℝ) ≤ y5 ∧ y5 ≤ (2500:ℝ) ∧ (2516:ℝ) ≤ x6 ∧ x6 ≤ (2673:ℝ) ∧ (2959:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
  have u0 : (2278:ℝ) ≤ x3 := by
    have hd : (y3-y5)^2 ≤ (1242:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x5)^2+(y3-y5)^2 := by nlinarith only [hT35]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1020:ℝ)) (D := (1242:ℝ))
      (xi := x3) (xj := x5) (yi := y3) (yj := y5)
      (ai := (2000:ℝ)) (aj := (1258:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact hx5U) (by exact hx5L) (by norm_num)
    linarith only [hh]
  have u1 : y3 ≤ (1564:ℝ) := by
    have hd : (x3-x6)^2 ≤ (722:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u0
      · exact hx3U
      · exact hx6L
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1436:ℝ)) (D := (722:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2516:ℝ)) (bi := (1742:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u2 : (2694:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (722:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact u0
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1436:ℝ)) (D := (722:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2516:ℝ)) (aj := (1258:ℝ)) (bj := (1564:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact u1) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u3 : y1 ≤ (138:ℝ) := by
    have hd : (x1-x3)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact hx1U
      · exact u0
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1258:ℝ)) (bi := (484:ℝ)) (bj := (1564:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy3L) (by exact u1) (by norm_num)
    linarith only [hh]
  have u4 : (1426:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u0
      · exact hx3U
      · exact hx1L
      · exact hx1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1258:ℝ)) (aj := (0:ℝ)) (bj := (138:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact u3) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u5 : (2454:ℝ) ≤ x3 := by
    have hd : (y3-y5)^2 ≤ (1074:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u4
      · exact u1
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x5)^2+(y3-y5)^2 := by nlinarith only [hT35]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1196:ℝ)) (D := (1074:ℝ))
      (xi := x3) (xj := x5) (yi := y3) (yj := y5)
      (ai := (2278:ℝ)) (aj := (1258:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u0) (by exact hx5U) (by exact hx5L) (by norm_num)
    linarith only [hh]
  have u6 : y3 ≤ (1488:ℝ) := by
    have hd : (x3-x6)^2 ≤ (546:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u5
      · exact hx3U
      · exact hx6L
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1512:ℝ)) (D := (546:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2694:ℝ)) (bi := (1564:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u1) (by exact u2) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u7 : (2938:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (546:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact u5
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1512:ℝ)) (D := (546:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2694:ℝ)) (aj := (1426:ℝ)) (bj := (1488:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u2) (by exact u6) (by exact u4) (by norm_num)
    linarith only [hh]
  have u8 : x1 ≤ (2392:ℝ) := by
    have hd : (y1-y3)^2 ≤ (1488:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u3
      · exact u4
      · exact u6
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (608:ℝ)) (D := (1488:ℝ))
      (xi := x1) (xj := x3) (yi := y1) (yj := y3)
      (aj := (2454:ℝ)) (bi := (3000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1U) (by exact u5) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u9 : y1 ≤ (62:ℝ) := by
    have hd : (x1-x3)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact u8
      · exact u5
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y3)^2+(x1-x3)^2 := by nlinarith only [hT13]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := y1) (xj := y3) (yi := x1) (yj := x3)
      (aj := (1426:ℝ)) (bi := (138:ℝ)) (bj := (1488:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u3) (by exact u4) (by exact u6) (by norm_num)
    linarith only [hh]
  have u10 : (2866:ℝ) ≤ x3 := by
    have hd : (y3-y1)^2 ≤ (1488:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u4
      · exact u6
      · exact hy1L
      · exact u9
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x1)^2+(y3-y1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (608:ℝ)) (D := (1488:ℝ))
      (xi := x3) (xj := x1) (yi := y3) (yj := y1)
      (ai := (2454:ℝ)) (aj := (2258:ℝ)) (bj := (2392:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u5) (by exact u8) (by exact hx1L) (by norm_num)
    linarith only [hh]
  have u11 : y3 ≤ (1467:ℝ) := by
    have hd : (x3-x6)^2 ≤ (484:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u10
      · exact hx3U
      · exact hx6L
      · exact hx6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y6)^2+(x3-x6)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1533:ℝ)) (D := (484:ℝ))
      (xi := y3) (xj := y6) (yi := x3) (yj := x6)
      (aj := (2938:ℝ)) (bi := (1488:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u6) (by exact u7) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u12 : x6 ≤ (2673:ℝ) := by
    have hd : (y6-y3)^2 ≤ (1574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u7
      · exact hy6U
      · exact u4
      · exact u11
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x3)^2+(y6-y3)^2 := by nlinarith only [hT36]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (327:ℝ)) (D := (1574:ℝ))
      (xi := x6) (xj := x3) (yi := y6) (yj := y3)
      (aj := (2866:ℝ)) (bi := (3000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6U) (by exact u10) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u13 : (2959:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (484:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact u12
      · exact u10
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1533:ℝ)) (D := (484:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2938:ℝ)) (aj := (1426:ℝ)) (bj := (1467:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u7) (by exact u11) (by exact u4) (by norm_num)
    linarith only [hh]
  have u14 : x0 ≤ (1134:ℝ) := by
    have hd : (y0-y1)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact hy0U
      · exact hy1L
      · exact u9
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x0-x1)^2+(y0-y1)^2 := by nlinarith only [hT01]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := x0) (xj := x1) (yi := y0) (yj := y1)
      (aj := (2258:ℝ)) (bi := (1742:ℝ)) (bj := (2392:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx0U) (by exact hx1L) (by exact u8) (by norm_num)
    linarith only [hh]
  have u15 : (804:ℝ) ≤ y0 := by
    have hd : (x0-x1)^2 ≤ (1392:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u14
      · exact hx1L
      · exact u8
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y0-y1)^2+(x0-x1)^2 := by nlinarith only [hT01]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (804:ℝ)) (D := (1392:ℝ))
      (xi := y0) (xj := y1) (yi := x0) (yj := x1)
      (ai := (0:ℝ)) (aj := (0:ℝ)) (bj := (62:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy0L) (by exact u9) (by exact hy1L) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, u14, u15, hy0U, hx1L, u8, hy1L, u9, hx2L, hx2U, hy2L, hy2U, u10, hx3U, u4, u11, hx4L, hx4U, hy4L, hy4U, hx5L, hx5U, hy5L, hy5U, hx6L, u12, u13, hy6U⟩
end N7LowCorrect
end CirclePackingConstants

namespace CirclePackingConstants
namespace N7High

/-- A continuous point enclosure with integer-originated real endpoints. -/
structure N7Box where
  xl : ℝ
  xu : ℝ
  yl : ℝ
  yu : ℝ

def N7Box.Contains (b : N7Box) (x y : ℝ) : Prop :=
  b.xl ≤ x ∧ x ≤ b.xu ∧ b.yl ≤ y ∧ y ≤ b.yu

def N7Box.setXL (b : N7Box) (z : ℝ) : N7Box := { b with xl := z }
def N7Box.setXU (b : N7Box) (z : ℝ) : N7Box := { b with xu := z }
def N7Box.setYL (b : N7Box) (z : ℝ) : N7Box := { b with yl := z }
def N7Box.setYU (b : N7Box) (z : ℝ) : N7Box := { b with yu := z }

lemma contains_setXL {b : N7Box} {x y z : ℝ}
    (h : b.Contains x y) (hz : z ≤ x) : (b.setXL z).Contains x y := by
  exact ⟨hz, h.2.1, h.2.2.1, h.2.2.2⟩
lemma contains_setXU {b : N7Box} {x y z : ℝ}
    (h : b.Contains x y) (hz : x ≤ z) : (b.setXU z).Contains x y := by
  exact ⟨h.1, hz, h.2.2.1, h.2.2.2⟩
lemma contains_setYL {b : N7Box} {x y z : ℝ}
    (h : b.Contains x y) (hz : z ≤ y) : (b.setYL z).Contains x y := by
  exact ⟨h.1, h.2.1, hz, h.2.2.2⟩
lemma contains_setYU {b : N7Box} {x y z : ℝ}
    (h : b.Contains x y) (hz : y ≤ z) : (b.setYU z).Contains x y := by
  exact ⟨h.1, h.2.1, h.2.2.1, hz⟩

/-- Closed midpoint children faithfully cover their parent enclosure. -/
lemma split_closed_cover {b : N7Box} {x y m : ℝ} (h : b.Contains x y)
    (hm : b.xl ≤ m) (hm' : m ≤ b.xu) :
    (b.setXU m).Contains x y ∨ (b.setXL m).Contains x y := by
  rcases le_total x m with hxm | hmx
  · exact Or.inl (contains_setXU h hxm)
  · exact Or.inr (contains_setXL h hmx)

/-- One terminal verifier test is sound: a box pair whose coordinate maxima
are bounded by `Dx,Dy` cannot contain a strictly-`T` separated pair. -/
lemma terminal_reject_sound {a b : N7Box} {x y u v Dx Dy T : ℝ}
    (ha : a.Contains x y) (hb : b.Contains u v)
    (hx : -Dx ≤ a.xl - b.xu) (hx' : a.xu - b.xl ≤ Dx)
    (hy : -Dy ≤ a.yl - b.yu) (hy' : a.yu - b.yl ≤ Dy)
    (hmax : Dx^2 + Dy^2 ≤ T) :
    ¬ T < (x-u)^2 + (y-v)^2 := by
  have hdx0 : 0 ≤ Dx := by
    have : a.xl - b.xu ≤ a.xu - b.xl := by linarith [ha.1, ha.2.1, hb.1, hb.2.1]
    linarith
  have hdy0 : 0 ≤ Dy := by
    have : a.yl - b.yu ≤ a.yu - b.yl := by linarith [ha.2.2.1, ha.2.2.2, hb.2.2.1, hb.2.2.2]
    linarith
  have hxl : -Dx ≤ x-u := by linarith [ha.1, hb.2.1]
  have hxu : x-u ≤ Dx := by linarith [ha.2.1, hb.1]
  have hyl : -Dy ≤ y-v := by linarith [ha.2.2.1, hb.2.2.2]
  have hyu : y-v ≤ Dy := by linarith [ha.2.2.2, hb.2.2.1]
  have hsx : (x-u)^2 ≤ Dx^2 := by nlinarith [mul_nonneg (show 0 ≤ Dx-(x-u) by linarith) (show 0 ≤ Dx+(x-u) by linarith)]
  have hsy : (y-v)^2 ≤ Dy^2 := by nlinarith [mul_nonneg (show 0 ≤ Dy-(y-v) by linarith) (show 0 ≤ Dy+(y-v) by linarith)]
  linarith


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
  (hx0L : (1000:ℝ) ≤ x0) (hx0U : x0 ≤ (1742:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (1000:ℝ))
  (hx1L : (2258:ℝ) ≤ x1) (hx1U : x1 ≤ (3000:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (484:ℝ))
  (hx2L : (0:ℝ) ≤ x2) (hx2U : x2 ≤ (1000:ℝ)) (hy2L : (1000:ℝ) ≤ y2) (hy2U : y2 ≤ (1742:ℝ))
  (hx3L : (2000:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1258:ℝ) ≤ y3) (hy3U : y3 ≤ (1742:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (484:ℝ)) (hy4L : (2258:ℝ) ≤ y4) (hy4U : y4 ≤ (3000:ℝ))
  (hx5L : (1258:ℝ) ≤ x5) (hx5U : x5 ≤ (1742:ℝ)) (hy5L : (2500:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2516:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2516:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (1000:ℝ) ≤ x0 ∧ x0 ≤ (1742:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (1000:ℝ) ∧ (2258:ℝ) ≤ x1 ∧ x1 ≤ (3000:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (484:ℝ) ∧ (863:ℝ) ≤ x2 ∧ x2 ≤ (1000:ℝ) ∧ (1000:ℝ) ≤ y2 ∧ y2 ≤ (1098:ℝ) ∧ (2289:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1258:ℝ) ≤ y3 ∧ y3 ≤ (1742:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (47:ℝ) ∧ (2258:ℝ) ≤ y4 ∧ y4 ≤ (2356:ℝ) ∧ (1426:ℝ) ≤ x5 ∧ x5 ≤ (1467:ℝ) ∧ (2902:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2959:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2516:ℝ) ≤ y6 ∧ y6 ≤ (2673:ℝ) := by
  have u0 : x4 ≤ (316:ℝ) := by
    have hd : (y4-y5)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact hy4U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1258:ℝ)) (bi := (484:ℝ)) (bj := (1742:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
    linarith only [hh]
  have u1 : (1426:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy5L
      · exact hy5U
      · exact hy4L
      · exact hy4U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1258:ℝ)) (aj := (0:ℝ)) (bj := (316:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5L) (by exact u0) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u2 : x5 ≤ (1473:ℝ) := by
    have hd : (y5-y6)^2 ≤ (500:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy5L
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1527:ℝ)) (D := (500:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2516:ℝ)) (bi := (1742:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u3 : (2953:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (500:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy6L
      · exact hy6U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1527:ℝ)) (D := (500:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2516:ℝ)) (aj := (1426:ℝ)) (bj := (1473:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact u2) (by exact u1) (by norm_num)
    linarith only [hh]
  have u4 : x4 ≤ (47:ℝ) := by
    have hd : (y4-y5)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy4L
      · exact hy4U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1426:ℝ)) (bi := (316:ℝ)) (bj := (1473:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u0) (by exact u1) (by exact u2) (by norm_num)
    linarith only [hh]
  have u5 : y4 ≤ (2356:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1473:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u4
      · exact u1
      · exact u2
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (644:ℝ)) (D := (1473:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2500:ℝ)) (bi := (3000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u6 : (2902:ℝ) ≤ y5 := by
    have hd : (x5-x4)^2 ≤ (1473:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u1
      · exact u2
      · exact hx4L
      · exact u4
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y4)^2+(x5-x4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (644:ℝ)) (D := (1473:ℝ))
      (xi := y5) (xj := y4) (yi := x5) (yj := x4)
      (ai := (2500:ℝ)) (aj := (2258:ℝ)) (bj := (2356:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact u5) (by exact hy4L) (by norm_num)
    linarith only [hh]
  have u7 : x5 ≤ (1467:ℝ) := by
    have hd : (y5-y6)^2 ≤ (484:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u6
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1533:ℝ)) (D := (484:ℝ))
      (xi := x5) (xj := x6) (yi := y5) (yj := y6)
      (aj := (2953:ℝ)) (bi := (1473:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u2) (by exact u3) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u8 : (2959:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (484:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy6L
      · exact hy6U
      · exact u6
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1533:ℝ)) (D := (484:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2953:ℝ)) (aj := (1426:ℝ)) (bj := (1467:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u3) (by exact u7) (by exact u1) (by norm_num)
    linarith only [hh]
  have u9 : y6 ≤ (2673:ℝ) := by
    have hd : (x6-x5)^2 ≤ (1574:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u8
      · exact hx6U
      · exact u1
      · exact u7
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y5)^2+(x6-x5)^2 := by nlinarith only [hT56]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (327:ℝ)) (D := (1574:ℝ))
      (xi := y6) (xj := y5) (yi := x6) (yj := x5)
      (aj := (2902:ℝ)) (bi := (3000:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6U) (by exact u6) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u10 : (863:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (1356:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy2L
      · exact hy2U
      · exact hy4L
      · exact u5
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (863:ℝ)) (D := (1356:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (0:ℝ)) (aj := (0:ℝ)) (bj := (47:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2L) (by exact u4) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u11 : y2 ≤ (1098:ℝ) := by
    have hd : (x2-x4)^2 ≤ (1000:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u10
      · exact hx2U
      · exact hx4L
      · exact u4
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y4)^2+(x2-x4)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1258:ℝ)) (D := (1000:ℝ))
      (xi := y2) (xj := y4) (yi := x2) (yj := x4)
      (aj := (2258:ℝ)) (bi := (1742:ℝ)) (bj := (2356:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2U) (by exact hy4L) (by exact u5) (by norm_num)
    linarith only [hh]
  have u12 : (2289:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (742:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact hy2L
      · exact u11
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1426:ℝ)) (D := (742:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2000:ℝ)) (aj := (863:ℝ)) (bj := (1000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact hx2U) (by exact u10) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, hx0U, hy0L, hy0U, hx1L, hx1U, hy1L, hy1U, u10, hx2U, hy2L, u11, u12, hx3U, hy3L, hy3U, hx4L, u4, hy4L, u5, u1, u7, u6, hy5U, u8, hx6U, hy6L, u9⟩
lemma high_terminal (x3 y3 x6 y6 : ℝ)
    (hx3L : (2289:ℝ) ≤ x3) (hx3U : x3 ≤ 3000)
    (hy3L : (1258:ℝ) ≤ y3) (hy3U : y3 ≤ 1742)
    (hx6L : (2959:ℝ) ≤ x6) (hx6U : x6 ≤ 3000)
    (hy6L : (2516:ℝ) ≤ y6) (hy6U : y6 ≤ 2673)
    (hT36 : (2584683:ℝ) < (x3-x6)^2+(y3-y6)^2) : False := by
  have h := terminal_reject_sound
    (a := {xl := (2289:ℝ), xu := 3000, yl := 1258, yu := 1742})
    (b := {xl := (2959:ℝ), xu := 3000, yl := 2516, yu := 2673})
    (x := x3) (y := y3) (u := x6) (v := y6)
    (Dx := (711:ℝ)) (Dy := (1415:ℝ)) (T := (2584683:ℝ))
    (by exact ⟨hx3L,hx3U,hy3L,hy3U⟩)
    (by exact ⟨hx6L,hx6U,hy6L,hy6U⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h hT36
end N7High
end CirclePackingConstants
namespace CirclePackingConstants
end CirclePackingConstants

open CirclePackingConstants

theorem solution (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L : (1000:ℝ) ≤ x0) (hx0U : x0 ≤ (2000:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (1000:ℝ))
  (hx1L : (2000:ℝ) ≤ x1) (hx1U : x1 ≤ (3000:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (1000:ℝ))
  (hx2L : (0:ℝ) ≤ x2) (hx2U : x2 ≤ (1000:ℝ)) (hy2L : (1000:ℝ) ≤ y2) (hy2U : y2 ≤ (2000:ℝ))
  (hx3L : (2000:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1000:ℝ) ≤ y3) (hy3U : y3 ≤ (2000:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (1000:ℝ)) (hy4L : (2000:ℝ) ≤ y4) (hy4U : y4 ≤ (3000:ℝ))
  (hx5L : (1000:ℝ) ≤ x5) (hx5U : x5 ≤ (2000:ℝ)) (hy5L : (2000:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2000:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2000:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
  (hhT01 : (2584683:ℝ) < (x0-x1)^2+(y0-y1)^2)
  (hhT02 : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2)
  (hhT03 : (2584683:ℝ) < (x0-x3)^2+(y0-y3)^2)
  (hhT04 : (2584683:ℝ) < (x0-x4)^2+(y0-y4)^2)
  (hhT05 : (2584683:ℝ) < (x0-x5)^2+(y0-y5)^2)
  (hhT06 : (2584683:ℝ) < (x0-x6)^2+(y0-y6)^2)
  (hhT12 : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2)
  (hhT13 : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2)
  (hhT14 : (2584683:ℝ) < (x1-x4)^2+(y1-y4)^2)
  (hhT15 : (2584683:ℝ) < (x1-x5)^2+(y1-y5)^2)
  (hhT16 : (2584683:ℝ) < (x1-x6)^2+(y1-y6)^2)
  (hhT23 : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2)
  (hhT24 : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2)
  (hhT25 : (2584683:ℝ) < (x2-x5)^2+(y2-y5)^2)
  (hhT26 : (2584683:ℝ) < (x2-x6)^2+(y2-y6)^2)
  (hhT34 : (2584683:ℝ) < (x3-x4)^2+(y3-y4)^2)
  (hhT35 : (2584683:ℝ) < (x3-x5)^2+(y3-y5)^2)
  (hhT36 : (2584683:ℝ) < (x3-x6)^2+(y3-y6)^2)
  (hhT45 : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2)
  (hhT46 : (2584683:ℝ) < (x4-x6)^2+(y4-y6)^2)
  (hhT56 : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2)
  : False := by
  have hr := N7Root.n7_stage_0 (x0 := x0) (y0 := y0) (x1 := x1) (y1 := y1) (x2 := x2) (y2 := y2) (x3 := x3) (y3 := y3) (x4 := x4) (y4 := y4) (x5 := x5) (y5 := y5) (x6 := x6) (y6 := y6) (hx0L := hx0L) (hx0U := hx0U) (hy0L := hy0L) (hy0U := hy0U) (hx1L := hx1L) (hx1U := hx1U) (hy1L := hy1L) (hy1U := hy1U) (hx2L := hx2L) (hx2U := hx2U) (hy2L := hy2L) (hy2U := hy2U) (hx3L := hx3L) (hx3U := hx3U) (hy3L := hy3L) (hy3U := hy3U) (hx4L := hx4L) (hx4U := hx4U) (hy4L := hy4L) (hy4U := hy4U) (hx5L := hx5L) (hx5U := hx5U) (hy5L := hy5L) (hy5U := hy5U) (hx6L := hx6L) (hx6U := hx6U) (hy6L := hy6L) (hy6U := hy6U) (hT01 := hhT01) (hT02 := hhT02) (hT03 := hhT03) (hT04 := hhT04) (hT05 := hhT05) (hT06 := hhT06) (hT12 := hhT12) (hT13 := hhT13) (hT14 := hhT14) (hT15 := hhT15) (hT16 := hhT16) (hT23 := hhT23) (hT24 := hhT24) (hT25 := hhT25) (hT26 := hhT26) (hT34 := hhT34) (hT35 := hhT35) (hT36 := hhT36) (hT45 := hhT45) (hT46 := hhT46) (hT56 := hhT56)
  rcases hr with ⟨hx0Lr, hx0Ur, hy0Lr, hy0Ur, hx1Lr, hx1Ur, hy1Lr, hy1Ur, hx2Lr, hx2Ur, hy2Lr, hy2Ur, hx3Lr, hx3Ur, hy3Lr, hy3Ur, hx4Lr, hx4Ur, hy4Lr, hy4Ur, hx5Lr, hx5Ur, hy5Lr, hy5Ur, hx6Lr, hx6Ur, hy6Lr, hy6Ur⟩
  rcases le_total y5 (2500:ℝ) with hlo | hhi
  · have hc := N7LowCorrect.n7_stage_0 (x0 := x0) (y0 := y0) (x1 := x1) (y1 := y1) (x2 := x2) (y2 := y2) (x3 := x3) (y3 := y3) (x4 := x4) (y4 := y4) (x5 := x5) (y5 := y5) (x6 := x6) (y6 := y6) (hT01 := hhT01) (hT02 := hhT02) (hT03 := hhT03) (hT04 := hhT04) (hT05 := hhT05) (hT06 := hhT06) (hT12 := hhT12) (hT13 := hhT13) (hT14 := hhT14) (hT15 := hhT15) (hT16 := hhT16) (hT23 := hhT23) (hT24 := hhT24) (hT25 := hhT25) (hT26 := hhT26) (hT34 := hhT34) (hT35 := hhT35) (hT36 := hhT36) (hT45 := hhT45) (hT46 := hhT46) (hT56 := hhT56) (hx0L := hx0Lr) (hx0U := hx0Ur) (hy0L := hy0Lr) (hy0U := hy0Ur) (hx1L := hx1Lr) (hx1U := hx1Ur) (hy1L := hy1Lr) (hy1U := hy1Ur) (hx2L := hx2Lr) (hx2U := hx2Ur) (hy2L := hy2Lr) (hy2U := hy2Ur) (hx3L := hx3Lr) (hx3U := hx3Ur) (hy3L := hy3Lr) (hy3U := hy3Ur) (hx4L := hx4Lr) (hx4U := hx4Ur) (hy4L := hy4Lr) (hy4U := hy4Ur) (hx5L := hx5Lr) (hx5U := hx5Ur) (hy5L := hy5Lr) (hx6L := hx6Lr) (hx6U := hx6Ur) (hy6L := hy6Lr) (hy6U := hy6Ur) (hy5U := hlo)
    rcases hc with ⟨hx0Lf,hx0Uf,hy0Lf,hy0Uf,hx1Lf,hx1Uf,hy1Lf,hy1Uf,hx2Lf,hx2Uf,hy2Lf,hy2Uf,hx3Lf,hx3Uf,hy3Lf,hy3Uf,hx4Lf,hx4Uf,hy4Lf,hy4Uf,hx5Lf,hx5Uf,hy5Lf,hy5Uf,hx6Lf,hx6Uf,hy6Lf,hy6Uf⟩
    have d0 : (x0-x2)^2 ≤ (1134:ℝ)^2 := by
      apply N7LowCorrect.sqdiff_bound_contract
      · exact hx0Lf
      · exact hx0Uf
      · exact hx2Lf
      · exact hx2Uf
      · norm_num
      · norm_num
    have d2 : (y0-y2)^2 ≤ (938:ℝ)^2 := by
      apply N7LowCorrect.sqdiff_bound_contract
      · exact hy0Lf
      · exact hy0Uf
      · exact hy2Lf
      · exact hy2Uf
      · norm_num
      · norm_num
    have hconst : (1134:ℝ)^2 + (938:ℝ)^2 < (2584683:ℝ) := by norm_num
    linarith only [hhT02, d0, d2, hconst]
  · have hc := N7High.n7_stage_0 (x0 := x0) (y0 := y0) (x1 := x1) (y1 := y1) (x2 := x2) (y2 := y2) (x3 := x3) (y3 := y3) (x4 := x4) (y4 := y4) (x5 := x5) (y5 := y5) (x6 := x6) (y6 := y6) (hT01 := hhT01) (hT02 := hhT02) (hT03 := hhT03) (hT04 := hhT04) (hT05 := hhT05) (hT06 := hhT06) (hT12 := hhT12) (hT13 := hhT13) (hT14 := hhT14) (hT15 := hhT15) (hT16 := hhT16) (hT23 := hhT23) (hT24 := hhT24) (hT25 := hhT25) (hT26 := hhT26) (hT34 := hhT34) (hT35 := hhT35) (hT36 := hhT36) (hT45 := hhT45) (hT46 := hhT46) (hT56 := hhT56) (hx0L := hx0Lr) (hx0U := hx0Ur) (hy0L := hy0Lr) (hy0U := hy0Ur) (hx1L := hx1Lr) (hx1U := hx1Ur) (hy1L := hy1Lr) (hy1U := hy1Ur) (hx2L := hx2Lr) (hx2U := hx2Ur) (hy2L := hy2Lr) (hy2U := hy2Ur) (hx3L := hx3Lr) (hx3U := hx3Ur) (hy3L := hy3Lr) (hy3U := hy3Ur) (hx4L := hx4Lr) (hx4U := hx4Ur) (hy4L := hy4Lr) (hy4U := hy4Ur) (hx5L := hx5Lr) (hx5U := hx5Ur) (hx6L := hx6Lr) (hx6U := hx6Ur) (hy6L := hy6Lr) (hy6U := hy6Ur) (hy5L := hhi) (hy5U := hy5Ur)
    rcases hc with ⟨hx0Lf,hx0Uf,hy0Lf,hy0Uf,hx1Lf,hx1Uf,hy1Lf,hy1Uf,hx2Lf,hx2Uf,hy2Lf,hy2Uf,hx3Lf,hx3Uf,hy3Lf,hy3Uf,hx4Lf,hx4Uf,hy4Lf,hy4Uf,hx5Lf,hx5Uf,hy5Lf,hy5Uf,hx6Lf,hx6Uf,hy6Lf,hy6Uf⟩
    exact N7High.high_terminal x3 y3 x6 y6 hx3Lf hx3Uf hy3Lf hy3Uf hx6Lf hx6Uf hy6Lf hy6Uf hhT36
