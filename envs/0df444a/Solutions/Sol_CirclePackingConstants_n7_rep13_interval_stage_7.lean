-- Prove2me | solution 1 for CirclePackingConstants.n7_rep13_interval_stage_7
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:22:30.962989+00:00
-- url     : https://prove2.me/submissions/c3abb141-a1b6-4d7c-857b-5fe68cd7c525

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
  (hx0L : (0:ℝ) ≤ x0) (hx0U : x0 ≤ (591:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (591:ℝ))
  (hx1L : (2183:ℝ) ≤ x1) (hx1U : x1 ≤ (2198:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (9:ℝ))
  (hx2L : (1385:ℝ) ≤ x2) (hx2U : x2 ≤ (1393:ℝ)) (hy2L : (1384:ℝ) ≤ y2) (hy2U : y2 ≤ (1393:ℝ))
  (hx3L : (2992:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1384:ℝ) ≤ y3) (hy3U : y3 ≤ (1393:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (8:ℝ)) (hy4L : (2180:ℝ) ≤ y4) (hy4U : y4 ≤ (2200:ℝ))
  (hx5L : (1382:ℝ) ≤ x5) (hx5U : x5 ≤ (1393:ℝ)) (hy5L : (2985:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2989:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2985:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (591:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (591:ℝ) ∧ (2190:ℝ) ≤ x1 ∧ x1 ≤ (2198:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (5:ℝ) ∧ (1388:ℝ) ≤ x2 ∧ x2 ≤ (1393:ℝ) ∧ (1388:ℝ) ≤ y2 ∧ y2 ≤ (1393:ℝ) ∧ (2995:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1388:ℝ) ≤ y3 ∧ y3 ≤ (1393:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (5:ℝ) ∧ (2190:ℝ) ≤ y4 ∧ y4 ≤ (2198:ℝ) ∧ (1388:ℝ) ≤ x5 ∧ x5 ≤ (1393:ℝ) ∧ (2995:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2995:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2995:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ) := by
  have u224 : (2186:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact hx4U
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2180:ℝ)) (aj := (1384:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4L) (by exact hy2U) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u225 : x4 ≤ (7:ℝ) := by
    have hd : (y4-y5)^2 ≤ (814:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u224
      · exact hy4U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1386:ℝ)) (D := (814:ℝ))
      (xi := x4) (xj := x5) (yi := y4) (yj := y5)
      (aj := (1382:ℝ)) (bi := (8:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
    linarith only [hh]
  have u226 : y4 ≤ (2198:ℝ) := by
    have hd : (x4-x5)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u225
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y5)^2+(x4-x5)^2 := by nlinarith only [hT45]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := y4) (xj := y5) (yi := x4) (yj := x5)
      (aj := (2985:ℝ)) (bi := (2200:ℝ)) (bj := (3000:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy4U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u227 : (2991:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (11:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (11:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2985:ℝ)) (aj := (1384:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy5L) (by exact hy2U) (by exact hy2L) (by norm_num)
    linarith only [hh]
  have u228 : (1386:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (814:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u227
      · exact hy5U
      · exact u224
      · exact u226
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1386:ℝ)) (D := (814:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1382:ℝ)) (aj := (0:ℝ)) (bj := (7:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx5L) (by exact u225) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u229 : (2991:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (11:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact hx3L
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (11:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2985:ℝ)) (aj := (1384:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy6L) (by exact hy3U) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u230 : (2993:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (9:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u229
      · exact hy6U
      · exact u227
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (9:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2989:ℝ)) (aj := (1386:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx6L) (by exact hx5U) (by exact u228) (by norm_num)
    linarith only [hh]
  have u231 : (2187:ℝ) ≤ x1 := by
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
      (ai := (2183:ℝ)) (aj := (1385:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx1L) (by exact hx2U) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have u232 : y1 ≤ (7:ℝ) := by
    have hd : (x1-x2)^2 ≤ (813:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u231
      · exact hx1U
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y2)^2+(x1-x2)^2 := by nlinarith only [hT12]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1386:ℝ)) (D := (813:ℝ))
      (xi := y1) (xj := y2) (yi := x1) (yj := x2)
      (aj := (1384:ℝ)) (bi := (9:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy1U) (by exact hy2L) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u233 : (1386:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (813:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact hx2U
      · exact u231
      · exact hx1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1386:ℝ)) (D := (813:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1384:ℝ)) (aj := (0:ℝ)) (bj := (7:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy2L) (by exact u232) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u234 : (1387:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (812:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u233
      · exact hy2U
      · exact u224
      · exact u226
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1387:ℝ)) (D := (812:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1385:ℝ)) (aj := (0:ℝ)) (bj := (7:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx2L) (by exact u225) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u235 : (1386:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (813:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx3L
      · exact hx3U
      · exact u231
      · exact hx1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1386:ℝ)) (D := (813:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1384:ℝ)) (aj := (0:ℝ)) (bj := (7:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hy3L) (by exact u232) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u236 : (2994:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (7:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u235
      · exact hy3U
      · exact u233
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (7:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2992:ℝ)) (aj := (1387:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact hx3L) (by exact hx2U) (by exact u234) (by norm_num)
    linarith only [hh]
  have u237 : x4 ≤ (6:ℝ) := by
    have hd : (y4-y2)^2 ≤ (812:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u224
      · exact u226
      · exact u233
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x2)^2+(y4-y2)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1387:ℝ)) (D := (812:ℝ))
      (xi := x4) (xj := x2) (yi := y4) (yj := y2)
      (aj := (1387:ℝ)) (bi := (7:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u225) (by exact u234) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u238 : (2188:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u237
      · exact u234
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2186:ℝ)) (aj := (1386:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u224) (by exact hy2U) (by exact u233) (by norm_num)
    linarith only [hh]
  have u239 : (2993:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (7:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u228
      · exact hx5U
      · exact u234
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (7:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2991:ℝ)) (aj := (1386:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u227) (by exact hy2U) (by exact u233) (by norm_num)
    linarith only [hh]
  have u240 : (1387:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (812:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u239
      · exact hy5U
      · exact u238
      · exact u226
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1387:ℝ)) (D := (812:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1386:ℝ)) (aj := (0:ℝ)) (bj := (6:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u228) (by exact u237) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u241 : (2993:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (7:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u230
      · exact hx6U
      · exact u236
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (7:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2991:ℝ)) (aj := (1386:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u229) (by exact hy3U) (by exact u235) (by norm_num)
    linarith only [hh]
  have u242 : (2994:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (7:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u241
      · exact hy6U
      · exact u239
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (7:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2993:ℝ)) (aj := (1387:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u230) (by exact hx5U) (by exact u240) (by norm_num)
    linarith only [hh]
  have u243 : (2189:ℝ) ≤ x1 := by
    have hd : (y1-y2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u232
      · exact u233
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := x1) (xj := x2) (yi := y1) (yj := y2)
      (ai := (2187:ℝ)) (aj := (1387:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u231) (by exact hx2U) (by exact u234) (by norm_num)
    linarith only [hh]
  have u244 : y1 ≤ (5:ℝ) := by
    have hd : (x1-x2)^2 ≤ (811:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u243
      · exact hx1U
      · exact u234
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y1-y2)^2+(x1-x2)^2 := by nlinarith only [hT12]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1388:ℝ)) (D := (811:ℝ))
      (xi := y1) (xj := y2) (yi := x1) (yj := x2)
      (aj := (1386:ℝ)) (bi := (7:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u232) (by exact u233) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u245 : (1388:ℝ) ≤ y2 := by
    have hd : (x2-x1)^2 ≤ (811:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u234
      · exact hx2U
      · exact u243
      · exact hx1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y2-y1)^2+(x2-x1)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1388:ℝ)) (D := (811:ℝ))
      (xi := y2) (xj := y1) (yi := x2) (yj := x1)
      (ai := (1386:ℝ)) (aj := (0:ℝ)) (bj := (5:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u233) (by exact u244) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u246 : (1388:ℝ) ≤ x2 := by
    have hd : (y2-y4)^2 ≤ (810:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u245
      · exact hy2U
      · exact u238
      · exact u226
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1388:ℝ)) (D := (810:ℝ))
      (xi := x2) (xj := x4) (yi := y2) (yj := y4)
      (ai := (1387:ℝ)) (aj := (0:ℝ)) (bj := (6:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u234) (by exact u237) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u247 : (1388:ℝ) ≤ y3 := by
    have hd : (x3-x1)^2 ≤ (811:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u236
      · exact hx3U
      · exact u243
      · exact hx1U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y3-y1)^2+(x3-x1)^2 := by nlinarith only [hT13]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1388:ℝ)) (D := (811:ℝ))
      (xi := y3) (xj := y1) (yi := x3) (yj := x1)
      (ai := (1386:ℝ)) (aj := (0:ℝ)) (bj := (5:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u235) (by exact u244) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u248 : (2995:ℝ) ≤ x3 := by
    have hd : (y3-y2)^2 ≤ (5:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u247
      · exact hy3U
      · exact u245
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x3-x2)^2+(y3-y2)^2 := by nlinarith only [hT23]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (5:ℝ))
      (xi := x3) (xj := x2) (yi := y3) (yj := y2)
      (ai := (2994:ℝ)) (aj := (1388:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u236) (by exact hx2U) (by exact u246) (by norm_num)
    linarith only [hh]
  have u249 : x4 ≤ (5:ℝ) := by
    have hd : (y4-y2)^2 ≤ (810:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u238
      · exact u226
      · exact u245
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x4-x2)^2+(y4-y2)^2 := by nlinarith only [hT24]
    have hh := force_upper_contract (T := (2584683:ℝ)) (q := (1388:ℝ)) (D := (810:ℝ))
      (xi := x4) (xj := x2) (yi := y4) (yj := y2)
      (aj := (1388:ℝ)) (bi := (6:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u237) (by exact u246) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u250 : (2190:ℝ) ≤ y4 := by
    have hd : (x4-x2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact u249
      · exact u246
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y4-y2)^2+(x4-x2)^2 := by nlinarith only [hT24]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := y4) (xj := y2) (yi := x4) (yj := x2)
      (ai := (2188:ℝ)) (aj := (1388:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u238) (by exact hy2U) (by exact u245) (by norm_num)
    linarith only [hh]
  have u251 : (2995:ℝ) ≤ y5 := by
    have hd : (x5-x2)^2 ≤ (6:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u240
      · exact hx5U
      · exact u246
      · exact hx2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y5-y2)^2+(x5-x2)^2 := by nlinarith only [hT25]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (6:ℝ))
      (xi := y5) (xj := y2) (yi := x5) (yj := x2)
      (ai := (2993:ℝ)) (aj := (1388:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u239) (by exact hy2U) (by exact u245) (by norm_num)
    linarith only [hh]
  have u252 : (1388:ℝ) ≤ x5 := by
    have hd : (y5-y4)^2 ≤ (810:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u251
      · exact hy5U
      · exact u250
      · exact u226
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x5-x4)^2+(y5-y4)^2 := by nlinarith only [hT45]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1388:ℝ)) (D := (810:ℝ))
      (xi := x5) (xj := x4) (yi := y5) (yj := y4)
      (ai := (1387:ℝ)) (aj := (0:ℝ)) (bj := (5:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u240) (by exact u249) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u253 : (2995:ℝ) ≤ y6 := by
    have hd : (x6-x3)^2 ≤ (6:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u242
      · exact hx6U
      · exact u248
      · exact hx3U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (y6-y3)^2+(x6-x3)^2 := by nlinarith only [hT36]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (6:ℝ))
      (xi := y6) (xj := y3) (yi := x6) (yj := x3)
      (ai := (2993:ℝ)) (aj := (1388:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u241) (by exact hy3U) (by exact u247) (by norm_num)
    linarith only [hh]
  have u254 : (2995:ℝ) ≤ x6 := by
    have hd : (y6-y5)^2 ≤ (5:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact u253
      · exact hy6U
      · exact u251
      · exact hy5U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x6-x5)^2+(y6-y5)^2 := by nlinarith only [hT56]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (1607:ℝ)) (D := (5:ℝ))
      (xi := x6) (xj := x5) (yi := y6) (yj := y5)
      (ai := (2994:ℝ)) (aj := (1388:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u242) (by exact hx5U) (by exact u252) (by norm_num)
    linarith only [hh]
  have u255 : (2190:ℝ) ≤ x1 := by
    have hd : (y1-y2)^2 ≤ (1393:ℝ)^2 := by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u244
      · exact u245
      · exact hy2U
      · norm_num
      · norm_num
    have hs : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2 := by nlinarith only [hT12]
    have hh := force_lower_contract (T := (2584683:ℝ)) (q := (802:ℝ)) (D := (1393:ℝ))
      (xi := x1) (xj := x2) (yi := y1) (yj := y2)
      (ai := (2189:ℝ)) (aj := (1388:ℝ)) (bj := (1393:ℝ))
      (by norm_num) hs hd (by norm_num)
      (by exact u243) (by exact hx2U) (by exact u246) (by norm_num)
    linarith only [hh]
  exact ⟨hx0L, hx0U, hy0L, hy0U, u255, hx1U, hy1L, u244, u246, hx2U, u245, hy2U, u248, hx3U, u247, hy3U, hx4L, u249, u250, u226, u252, hx5U, u251, hy5U, u254, hx6U, u253, hy6U⟩
