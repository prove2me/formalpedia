-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_14_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T00:30:35.318798+00:00
-- url     : https://prove2.me/submissions/7eb84382-a0c4-442c-bd72-43963ee082c6

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
noncomputable section
namespace CirclePackingConstants
namespace N7Rep14Stages

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

lemma n7_root_0 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(1000:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(1000:ℝ))
 (hx1L:(2000:ℝ)≤x1 ) (hx1U:x1≤(3000:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(1000:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(1000:ℝ) ) (hy2L:(1000:ℝ)≤y2 ) (hy2U:y2≤(2000:ℝ))
 (hx3L:(2000:ℝ)≤x3 ) (hx3U:x3≤(3000:ℝ) ) (hy3L:(1000:ℝ)≤y3 ) (hy3U:y3≤(2000:ℝ))
 (hx4L:(0:ℝ)≤x4 ) (hx4U:x4≤(1000:ℝ) ) (hy4L:(2000:ℝ)≤y4 ) (hy4U:y4≤(3000:ℝ))
 (hx5L:(1000:ℝ)≤x5 ) (hx5U:x5≤(2000:ℝ) ) (hy5L:(2000:ℝ)≤y5 ) (hy5U:y5≤(3000:ℝ))
 (hx6L:(2000:ℝ)≤x6 ) (hx6U:x6≤(3000:ℝ) ) (hy6L:(2000:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (0:ℝ)≤x0 ∧ x0≤(1000:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(484:ℝ) ∧ (2000:ℝ)≤x1 ∧ x1≤(3000:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(484:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(1000:ℝ) ∧ (1258:ℝ)≤y2 ∧ y2≤(1742:ℝ) ∧ (2000:ℝ)≤x3 ∧ x3≤(3000:ℝ) ∧ (1258:ℝ)≤y3 ∧ y3≤(1742:ℝ) ∧ (0:ℝ)≤x4 ∧ x4≤(484:ℝ) ∧ (2516:ℝ)≤y4 ∧ y4≤(3000:ℝ) ∧ (1258:ℝ)≤x5 ∧ x5≤(1742:ℝ) ∧ (2000:ℝ)≤y5 ∧ y5≤(3000:ℝ) ∧ (2516:ℝ)≤x6 ∧ x6≤(3000:ℝ) ∧ (2516:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: y0≤(742:ℝ):=by
  have hd:(x0-x2)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact hx0U
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1000:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(2000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
  linarith only [hh]
 have u1: y1≤(742:ℝ):=by
  have hd:(x1-x3)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact hx1U
   · exact hx3L
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y3)^2+(x1-x3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y1 ) (xj:=y3 ) (yi:=x1 ) (yj:=x3 ) (aj:=(1000:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(2000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy3L) (by exact hy3U) (by norm_num)
  linarith only [hh]
 have u2: (1258:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact hx2U
   · exact hx0L
   · exact hx0U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1000:ℝ) ) (aj:=(0:ℝ) ) (bj:=(742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2L) (by exact u0) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u3: y2≤(1742:ℝ):=by
  have hd:(x2-x4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact hx2U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y4)^2+(x2-x4)^2:=by nlinarith only [hT24]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y2 ) (xj:=y4 ) (yi:=x2 ) (yj:=x4 ) (aj:=(2000:ℝ) ) (bi:=(2000:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact hy4L) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u4: (1258:ℝ)≤y3:=by
  have hd:(x3-x1)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx3L
   · exact hx3U
   · exact hx1L
   · exact hx1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y1)^2+(x3-x1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y3 ) (xj:=y1 ) (yi:=x3 ) (yj:=x1 ) (ai:=(1000:ℝ) ) (aj:=(0:ℝ) ) (bj:=(742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3L) (by exact u1) (by exact hy1L) (by norm_num)
  linarith only [hh]
 have u5: y3≤(1742:ℝ):=by
  have hd:(x3-x6)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx3L
   · exact hx3U
   · exact hx6L
   · exact hx6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y6)^2+(x3-x6)^2:=by nlinarith only [hT36]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y3 ) (xj:=y6 ) (yi:=x3 ) (yj:=x6 ) (aj:=(2000:ℝ) ) (bi:=(2000:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
  linarith only [hh]
 have u6: (2516:ℝ)≤y4:=by
  have hd:(x4-x2)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx4L
   · exact hx4U
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y2)^2+(x4-x2)^2:=by nlinarith only [hT24]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y4 ) (xj:=y2 ) (yi:=x4 ) (yj:=x2 ) (ai:=(2000:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact u3) (by exact u2) (by norm_num)
  linarith only [hh]
 have u7: x4≤(742:ℝ):=by
  have hd:(y4-y5)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u6
   · exact hy4U
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x5)^2+(y4-y5)^2:=by nlinarith only [hT45]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x4 ) (xj:=x5 ) (yi:=y4 ) (yj:=y5 ) (aj:=(1000:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(2000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
  linarith only [hh]
 have u8: (1258:ℝ)≤x5:=by
  have hd:(y5-y4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy5L
   · exact hy5U
   · exact u6
   · exact hy4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x4)^2+(y5-y4)^2:=by nlinarith only [hT45]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x5 ) (xj:=x4 ) (yi:=y5 ) (yj:=y4 ) (ai:=(1000:ℝ) ) (aj:=(0:ℝ) ) (bj:=(742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5L) (by exact u7) (by exact hx4L) (by norm_num)
  linarith only [hh]
 have u9: x5≤(1742:ℝ):=by
  have hd:(y5-y6)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy5L
   · exact hy5U
   · exact hy6L
   · exact hy6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x6)^2+(y5-y6)^2:=by nlinarith only [hT56]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x5 ) (xj:=x6 ) (yi:=y5 ) (yj:=y6 ) (aj:=(2000:ℝ) ) (bi:=(2000:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
  linarith only [hh]
 have u10: (2516:ℝ)≤y6:=by
  have hd:(x6-x3)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact hx6U
   · exact hx3L
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y3)^2+(x6-x3)^2:=by nlinarith only [hT36]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y6 ) (xj:=y3 ) (yi:=x6 ) (yj:=x3 ) (ai:=(2000:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact u5) (by exact u4) (by norm_num)
  linarith only [hh]
 have u11: (2516:ℝ)≤x6:=by
  have hd:(y6-y5)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u10
   · exact hy6U
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x5)^2+(y6-y5)^2:=by nlinarith only [hT56]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x6 ) (xj:=x5 ) (yi:=y6 ) (yj:=y5 ) (ai:=(2000:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx6L) (by exact u9) (by exact u8) (by norm_num)
  linarith only [hh]
 have u12: y0≤(484:ℝ):=by
  have hd:(x0-x2)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact hx0U
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1258:ℝ) ) (bi:=(742:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact u2) (by exact u3) (by norm_num)
  linarith only [hh]
 have u13: y1≤(484:ℝ):=by
  have hd:(x1-x3)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact hx1U
   · exact hx3L
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y3)^2+(x1-x3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y1 ) (xj:=y3 ) (yi:=x1 ) (yj:=x3 ) (aj:=(1258:ℝ) ) (bi:=(742:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u4) (by exact u5) (by norm_num)
  linarith only [hh]
 have u14: x4≤(484:ℝ):=by
  have hd:(y4-y5)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u6
   · exact hy4U
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x5)^2+(y4-y5)^2:=by nlinarith only [hT45]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x4 ) (xj:=x5 ) (yi:=y4 ) (yj:=y5 ) (aj:=(1258:ℝ) ) (bi:=(742:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u7) (by exact u8) (by exact u9) (by norm_num)
  linarith only [hh]
 exact ⟨hx0L,hx0U,hy0L,u12,hx1L,hx1U,hy1L,u13,hx2L,hx2U,u2,u3,hx3L,hx3U,u4,u5,hx4L,u14,u6,hy4U,u8,u9,hy5L,hy5U,u11,hx6U,u10,hy6U⟩
lemma n7_root_lo_0 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(1000:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(484:ℝ))
 (hx1L:(2000:ℝ)≤x1 ) (hx1U:x1≤(3000:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(484:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(1000:ℝ) ) (hy2L:(1258:ℝ)≤y2 ) (hy2U:y2≤(1742:ℝ))
 (hx3L:(2000:ℝ)≤x3 ) (hx3U:x3≤(3000:ℝ) ) (hy3L:(1258:ℝ)≤y3 ) (hy3U:y3≤(1742:ℝ))
 (hx4L:(0:ℝ)≤x4 ) (hx4U:x4≤(484:ℝ) ) (hy4L:(2516:ℝ)≤y4 ) (hy4U:y4≤(3000:ℝ))
 (hx5L:(1258:ℝ)≤x5 ) (hx5U:x5≤(1742:ℝ) ) (hy5L:(2000:ℝ)≤y5 ) (hy5U:y5≤(2500:ℝ))
 (hx6L:(2516:ℝ)≤x6 ) (hx6U:x6≤(3000:ℝ) ) (hy6L:(2516:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (0:ℝ)≤x0 ∧ x0≤(1000:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(306:ℝ) ∧ (2000:ℝ)≤x1 ∧ x1≤(3000:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(306:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(722:ℝ) ∧ (1258:ℝ)≤y2 ∧ y2≤(1564:ℝ) ∧ (2278:ℝ)≤x3 ∧ x3≤(3000:ℝ) ∧ (1258:ℝ)≤y3 ∧ y3≤(1564:ℝ) ∧ (0:ℝ)≤x4 ∧ x4≤(484:ℝ) ∧ (2694:ℝ)≤y4 ∧ y4≤(3000:ℝ) ∧ (1258:ℝ)≤x5 ∧ x5≤(1742:ℝ) ∧ (2000:ℝ)≤y5 ∧ y5≤(2500:ℝ) ∧ (2516:ℝ)≤x6 ∧ x6≤(3000:ℝ) ∧ (2694:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: x2≤(722:ℝ):=by
  have hd:(y2-y5)^2≤(1242:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy2L
   · exact hy2U
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x5)^2+(y2-y5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1020:ℝ) ) (D:=(1242:ℝ) ) (xi:=x2 ) (xj:=x5 ) (yi:=y2 ) (yj:=y5 ) (aj:=(1258:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact hx5L) (by exact hx5U) (by norm_num)
  linarith only [hh]
 have u1: (2278:ℝ)≤x3:=by
  have hd:(y3-y5)^2≤(1242:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact hy3U
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x5)^2+(y3-y5)^2:=by nlinarith only [hT35]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1020:ℝ) ) (D:=(1242:ℝ) ) (xi:=x3 ) (xj:=x5 ) (yi:=y3 ) (yj:=y5 ) (ai:=(2000:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact hx5U) (by exact hx5L) (by norm_num)
  linarith only [hh]
 have u2: y3≤(1564:ℝ):=by
  have hd:(x3-x6)^2≤(722:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u1
   · exact hx3U
   · exact hx6L
   · exact hx6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y6)^2+(x3-x6)^2:=by nlinarith only [hT36]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1436:ℝ) ) (D:=(722:ℝ) ) (xi:=y3 ) (xj:=y6 ) (yi:=x3 ) (yj:=x6 ) (aj:=(2516:ℝ) ) (bi:=(1742:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
  linarith only [hh]
 have u3: (2694:ℝ)≤y4:=by
  have hd:(x4-x2)^2≤(722:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx4L
   · exact hx4U
   · exact hx2L
   · exact u0
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y2)^2+(x4-x2)^2:=by nlinarith only [hT24]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1436:ℝ) ) (D:=(722:ℝ) ) (xi:=y4 ) (xj:=y2 ) (yi:=x4 ) (yj:=x2 ) (ai:=(2516:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact hy2U) (by exact hy2L) (by norm_num)
  linarith only [hh]
 have u4: (2694:ℝ)≤y6:=by
  have hd:(x6-x3)^2≤(722:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact hx6U
   · exact u1
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y3)^2+(x6-x3)^2:=by nlinarith only [hT36]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1436:ℝ) ) (D:=(722:ℝ) ) (xi:=y6 ) (xj:=y3 ) (yi:=x6 ) (yj:=x3 ) (ai:=(2516:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1564:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact u2) (by exact hy3L) (by norm_num)
  linarith only [hh]
 have u5: y1≤(306:ℝ):=by
  have hd:(x1-x3)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact hx1U
   · exact u1
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y3)^2+(x1-x3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y1 ) (xj:=y3 ) (yi:=x1 ) (yj:=x3 ) (aj:=(1258:ℝ) ) (bi:=(484:ℝ) ) (bj:=(1564:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy3L) (by exact u2) (by norm_num)
  linarith only [hh]
 have u6: y2≤(1564:ℝ):=by
  have hd:(x2-x4)^2≤(722:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u0
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y4)^2+(x2-x4)^2:=by nlinarith only [hT24]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1436:ℝ) ) (D:=(722:ℝ) ) (xi:=y2 ) (xj:=y4 ) (yi:=x2 ) (yj:=x4 ) (aj:=(2694:ℝ) ) (bi:=(1742:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact u3) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u7: y0≤(306:ℝ):=by
  have hd:(x0-x2)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact hx0U
   · exact hx2L
   · exact u0
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1258:ℝ) ) (bi:=(484:ℝ) ) (bj:=(1564:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy0U) (by exact hy2L) (by exact u6) (by norm_num)
  linarith only [hh]
 exact ⟨hx0L,hx0U,hy0L,u7,hx1L,hx1U,hy1L,u5,hx2L,u0,hy2L,u6,u1,hx3U,hy3L,u2,hx4L,hx4U,u3,hy4U,hx5L,hx5U,hy5L,hy5U,hx6L,hx6U,u4,hy6U⟩
lemma n7_root_lo_lo_0 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(1000:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(306:ℝ))
 (hx1L:(2000:ℝ)≤x1 ) (hx1U:x1≤(2500:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(306:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(722:ℝ) ) (hy2L:(1258:ℝ)≤y2 ) (hy2U:y2≤(1564:ℝ))
 (hx3L:(2278:ℝ)≤x3 ) (hx3U:x3≤(3000:ℝ) ) (hy3L:(1258:ℝ)≤y3 ) (hy3U:y3≤(1564:ℝ))
 (hx4L:(0:ℝ)≤x4 ) (hx4U:x4≤(484:ℝ) ) (hy4L:(2694:ℝ)≤y4 ) (hy4U:y4≤(3000:ℝ))
 (hx5L:(1258:ℝ)≤x5 ) (hx5U:x5≤(1742:ℝ) ) (hy5L:(2000:ℝ)≤y5 ) (hy5U:y5≤(2500:ℝ))
 (hx6L:(2516:ℝ)≤x6 ) (hx6U:x6≤(3000:ℝ) ) (hy6L:(2694:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (603:ℝ)≤x0 ∧ x0≤(749:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(68:ℝ) ∧ (2000:ℝ)≤x1 ∧ x1≤(2343:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(209:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(550:ℝ) ∧ (1422:ℝ)≤y2 ∧ y2≤(1490:ℝ) ∧ (2657:ℝ)≤x3 ∧ x3≤(3000:ℝ) ∧ (1258:ℝ)≤y3 ∧ y3≤(1467:ℝ) ∧ (0:ℝ)≤x4 ∧ x4≤(484:ℝ) ∧ (2932:ℝ)≤y4 ∧ y4≤(3000:ℝ) ∧ (1258:ℝ)≤x5 ∧ x5≤(1742:ℝ) ∧ (2000:ℝ)≤y5 ∧ y5≤(2500:ℝ) ∧ (2516:ℝ)≤x6 ∧ x6≤(3000:ℝ) ∧ (2791:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: x0≤(922:ℝ):=by
  have hd:(y0-y1)^2≤(306:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact hy0U
   · exact hy1L
   · exact hy1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2:=by nlinarith only [hT01]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1578:ℝ) ) (D:=(306:ℝ) ) (xi:=x0 ) (xj:=x1 ) (yi:=y0 ) (yj:=y1 ) (aj:=(2000:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(2500:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0U) (by exact hx1L) (by exact hx1U) (by norm_num)
  linarith only [hh]
 have u1: y0≤(247:ℝ):=by
  have hd:(x0-x2)^2≤(922:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact u0
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1317:ℝ) ) (D:=(922:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1258:ℝ) ) (bi:=(306:ℝ) ) (bj:=(1564:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
  linarith only [hh]
 have u2: (1317:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(922:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact hx2U
   · exact hx0L
   · exact u0
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1317:ℝ) ) (D:=(922:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1258:ℝ) ) (aj:=(0:ℝ) ) (bj:=(247:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2L) (by exact u1) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u3: x2≤(654:ℝ):=by
  have hd:(y2-y5)^2≤(1183:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u2
   · exact hy2U
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x5)^2+(y2-y5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1088:ℝ) ) (D:=(1183:ℝ) ) (xi:=x2 ) (xj:=x5 ) (yi:=y2 ) (yj:=y5 ) (aj:=(1258:ℝ) ) (bi:=(722:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact hx5L) (by exact hx5U) (by norm_num)
  linarith only [hh]
 have u4: (2372:ℝ)≤x3:=by
  have hd:(y3-y1)^2≤(1564:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact hy3U
   · exact hy1L
   · exact hy1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x1)^2+(y3-y1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(372:ℝ) ) (D:=(1564:ℝ) ) (xi:=x3 ) (xj:=x1 ) (yi:=y3 ) (yj:=y1 ) (ai:=(2278:ℝ) ) (aj:=(2000:ℝ) ) (bj:=(2500:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact hx1U) (by exact hx1L) (by norm_num)
  linarith only [hh]
 have u5: y3≤(1521:ℝ):=by
  have hd:(x3-x6)^2≤(628:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u4
   · exact hx3U
   · exact hx6L
   · exact hx6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y6)^2+(x3-x6)^2:=by nlinarith only [hT36]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1479:ℝ) ) (D:=(628:ℝ) ) (xi:=y3 ) (xj:=y6 ) (yi:=x3 ) (yj:=x6 ) (aj:=(2694:ℝ) ) (bi:=(1564:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
  linarith only [hh]
 have u6: (2785:ℝ)≤y4:=by
  have hd:(x4-x2)^2≤(654:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx4L
   · exact hx4U
   · exact hx2L
   · exact u3
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y2)^2+(x4-x2)^2:=by nlinarith only [hT24]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1468:ℝ) ) (D:=(654:ℝ) ) (xi:=y4 ) (xj:=y2 ) (yi:=x4 ) (yj:=x2 ) (ai:=(2694:ℝ) ) (aj:=(1317:ℝ) ) (bj:=(1564:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact hy2U) (by exact u2) (by norm_num)
  linarith only [hh]
 have u7: (2737:ℝ)≤y6:=by
  have hd:(x6-x3)^2≤(628:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact hx6U
   · exact u4
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y3)^2+(x6-x3)^2:=by nlinarith only [hT36]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1479:ℝ) ) (D:=(628:ℝ) ) (xi:=y6 ) (xj:=y3 ) (yi:=x6 ) (yj:=x3 ) (ai:=(2694:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1521:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact u5) (by exact hy3L) (by norm_num)
  linarith only [hh]
 have u8: x1≤(2480:ℝ):=by
  have hd:(y1-y3)^2≤(1521:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact hy1U
   · exact hy3L
   · exact u5
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x3)^2+(y1-y3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(520:ℝ) ) (D:=(1521:ℝ) ) (xi:=x1 ) (xj:=x3 ) (yi:=y1 ) (yj:=y3 ) (aj:=(2372:ℝ) ) (bi:=(2500:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx1U) (by exact u4) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u9: y1≤(263:ℝ):=by
  have hd:(x1-x3)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact u8
   · exact u4
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y3)^2+(x1-x3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y1 ) (xj:=y3 ) (yi:=x1 ) (yj:=x3 ) (aj:=(1258:ℝ) ) (bi:=(306:ℝ) ) (bj:=(1521:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy3L) (by exact u5) (by norm_num)
  linarith only [hh]
 have u10: y2≤(1532:ℝ):=by
  have hd:(x2-x4)^2≤(654:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u3
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y4)^2+(x2-x4)^2:=by nlinarith only [hT24]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1468:ℝ) ) (D:=(654:ℝ) ) (xi:=y2 ) (xj:=y4 ) (yi:=x2 ) (yj:=x4 ) (aj:=(2785:ℝ) ) (bi:=(1564:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact u6) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u11: (2520:ℝ)≤x3:=by
  have hd:(y3-y1)^2≤(1521:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact u5
   · exact hy1L
   · exact u9
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x1)^2+(y3-y1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(520:ℝ) ) (D:=(1521:ℝ) ) (xi:=x3 ) (xj:=x1 ) (yi:=y3 ) (yj:=y1 ) (ai:=(2372:ℝ) ) (aj:=(2000:ℝ) ) (bj:=(2480:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u4) (by exact u8) (by exact hx1L) (by norm_num)
  linarith only [hh]
 have u12: y3≤(1467:ℝ):=by
  have hd:(x3-x6)^2≤(484:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u11
   · exact hx3U
   · exact hx6L
   · exact hx6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y6)^2+(x3-x6)^2:=by nlinarith only [hT36]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1533:ℝ) ) (D:=(484:ℝ) ) (xi:=y3 ) (xj:=y6 ) (yi:=x3 ) (yj:=x6 ) (aj:=(2737:ℝ) ) (bi:=(1521:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u5) (by exact u7) (by exact hy6U) (by norm_num)
  linarith only [hh]
 have u13: (2791:ℝ)≤y6:=by
  have hd:(x6-x3)^2≤(484:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact hx6U
   · exact u11
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y3)^2+(x6-x3)^2:=by nlinarith only [hT36]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1533:ℝ) ) (D:=(484:ℝ) ) (xi:=y6 ) (xj:=y3 ) (yi:=x6 ) (yj:=x3 ) (ai:=(2737:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1467:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u7) (by exact u12) (by exact hy3L) (by norm_num)
  linarith only [hh]
 have u14: x0≤(894:ℝ):=by
  have hd:(y0-y1)^2≤(263:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact u1
   · exact hy1L
   · exact u9
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2:=by nlinarith only [hT01]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1586:ℝ) ) (D:=(263:ℝ) ) (xi:=x0 ) (xj:=x1 ) (yi:=y0 ) (yj:=y1 ) (aj:=(2000:ℝ) ) (bi:=(922:ℝ) ) (bj:=(2480:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact hx1L) (by exact u8) (by norm_num)
  linarith only [hh]
 have u15: y0≤(196:ℝ):=by
  have hd:(x0-x2)^2≤(894:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact u14
   · exact hx2L
   · exact u3
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1336:ℝ) ) (D:=(894:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1317:ℝ) ) (bi:=(247:ℝ) ) (bj:=(1532:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u2) (by exact u10) (by norm_num)
  linarith only [hh]
 have u16: x1≤(2343:ℝ):=by
  have hd:(y1-y3)^2≤(1467:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact u9
   · exact hy3L
   · exact u12
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x3)^2+(y1-y3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(657:ℝ) ) (D:=(1467:ℝ) ) (xi:=x1 ) (xj:=x3 ) (yi:=y1 ) (yj:=y3 ) (aj:=(2520:ℝ) ) (bi:=(2480:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u8) (by exact u11) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u17: y1≤(209:ℝ):=by
  have hd:(x1-x3)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact u16
   · exact u11
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y3)^2+(x1-x3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y1 ) (xj:=y3 ) (yi:=x1 ) (yj:=x3 ) (aj:=(1258:ℝ) ) (bi:=(263:ℝ) ) (bj:=(1467:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u9) (by exact hy3L) (by exact u12) (by norm_num)
  linarith only [hh]
 have u18: (1336:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(894:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u3
   · exact hx0L
   · exact u14
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1336:ℝ) ) (D:=(894:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1317:ℝ) ) (aj:=(0:ℝ) ) (bj:=(196:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u2) (by exact u15) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u19: x2≤(634:ℝ):=by
  have hd:(y2-y5)^2≤(1164:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u18
   · exact u10
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x5)^2+(y2-y5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1108:ℝ) ) (D:=(1164:ℝ) ) (xi:=x2 ) (xj:=x5 ) (yi:=y2 ) (yj:=y5 ) (aj:=(1258:ℝ) ) (bi:=(654:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u3) (by exact hx5L) (by exact hx5U) (by norm_num)
  linarith only [hh]
 have u20: (2657:ℝ)≤x3:=by
  have hd:(y3-y1)^2≤(1467:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact u12
   · exact hy1L
   · exact u17
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x1)^2+(y3-y1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(657:ℝ) ) (D:=(1467:ℝ) ) (xi:=x3 ) (xj:=x1 ) (yi:=y3 ) (yj:=y1 ) (ai:=(2520:ℝ) ) (aj:=(2000:ℝ) ) (bj:=(2343:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u11) (by exact u16) (by exact hx1L) (by norm_num)
  linarith only [hh]
 have u21: (2813:ℝ)≤y4:=by
  have hd:(x4-x2)^2≤(634:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx4L
   · exact hx4U
   · exact hx2L
   · exact u19
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y2)^2+(x4-x2)^2:=by nlinarith only [hT24]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1477:ℝ) ) (D:=(634:ℝ) ) (xi:=y4 ) (xj:=y2 ) (yi:=x4 ) (yj:=x2 ) (ai:=(2785:ℝ) ) (aj:=(1336:ℝ) ) (bj:=(1532:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u6) (by exact u10) (by exact u18) (by norm_num)
  linarith only [hh]
 have u22: x0≤(749:ℝ):=by
  have hd:(y0-y1)^2≤(209:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact u15
   · exact hy1L
   · exact u17
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2:=by nlinarith only [hT01]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1594:ℝ) ) (D:=(209:ℝ) ) (xi:=x0 ) (xj:=x1 ) (yi:=y0 ) (yj:=y1 ) (aj:=(2000:ℝ) ) (bi:=(894:ℝ) ) (bj:=(2343:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u14) (by exact hx1L) (by exact u16) (by norm_num)
  linarith only [hh]
 have u23: y0≤(110:ℝ):=by
  have hd:(x0-x2)^2≤(749:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact u22
   · exact hx2L
   · exact u19
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1422:ℝ) ) (D:=(749:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1336:ℝ) ) (bi:=(196:ℝ) ) (bj:=(1532:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u15) (by exact u18) (by exact u10) (by norm_num)
  linarith only [hh]
 have u24: (1422:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(749:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u19
   · exact hx0L
   · exact u22
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1422:ℝ) ) (D:=(749:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1336:ℝ) ) (aj:=(0:ℝ) ) (bj:=(110:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u18) (by exact u23) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u25: y2≤(1523:ℝ):=by
  have hd:(x2-x4)^2≤(634:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u19
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y4)^2+(x2-x4)^2:=by nlinarith only [hT24]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1477:ℝ) ) (D:=(634:ℝ) ) (xi:=y2 ) (xj:=y4 ) (yi:=x2 ) (yj:=x4 ) (aj:=(2813:ℝ) ) (bi:=(1532:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u10) (by exact u21) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u26: x2≤(550:ℝ):=by
  have hd:(y2-y5)^2≤(1078:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u24
   · exact u25
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x5)^2+(y2-y5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1192:ℝ) ) (D:=(1078:ℝ) ) (xi:=x2 ) (xj:=x5 ) (yi:=y2 ) (yj:=y5 ) (aj:=(1258:ℝ) ) (bi:=(634:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u19) (by exact hx5L) (by exact hx5U) (by norm_num)
  linarith only [hh]
 have u27: (2932:ℝ)≤y4:=by
  have hd:(x4-x2)^2≤(550:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx4L
   · exact hx4U
   · exact hx2L
   · exact u26
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y2)^2+(x4-x2)^2:=by nlinarith only [hT24]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1510:ℝ) ) (D:=(550:ℝ) ) (xi:=y4 ) (xj:=y2 ) (yi:=x4 ) (yj:=x2 ) (ai:=(2813:ℝ) ) (aj:=(1422:ℝ) ) (bj:=(1523:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u21) (by exact u25) (by exact u24) (by norm_num)
  linarith only [hh]
 have u28: y0≤(101:ℝ):=by
  have hd:(x0-x2)^2≤(749:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact u22
   · exact hx2L
   · exact u26
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1422:ℝ) ) (D:=(749:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1422:ℝ) ) (bi:=(110:ℝ) ) (bj:=(1523:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u23) (by exact u24) (by exact u25) (by norm_num)
  linarith only [hh]
 have u29: y2≤(1490:ℝ):=by
  have hd:(x2-x4)^2≤(550:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u26
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y4)^2+(x2-x4)^2:=by nlinarith only [hT24]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1510:ℝ) ) (D:=(550:ℝ) ) (xi:=y2 ) (xj:=y4 ) (yi:=x2 ) (yj:=x4 ) (aj:=(2932:ℝ) ) (bi:=(1523:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u25) (by exact u27) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u30: (603:ℝ)≤x0:=by
  have hd:(y0-y2)^2≤(1490:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact u28
   · exact u24
   · exact u29
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x2)^2+(y0-y2)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(603:ℝ) ) (D:=(1490:ℝ) ) (xi:=x0 ) (xj:=x2 ) (yi:=y0 ) (yj:=y2 ) (ai:=(0:ℝ) ) (aj:=(0:ℝ) ) (bj:=(550:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0L) (by exact u26) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u31: y0≤(68:ℝ):=by
  have hd:(x0-x2)^2≤(749:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u30
   · exact u22
   · exact hx2L
   · exact u26
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1422:ℝ) ) (D:=(749:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1422:ℝ) ) (bi:=(101:ℝ) ) (bj:=(1490:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u28) (by exact u24) (by exact u29) (by norm_num)
  linarith only [hh]
 exact ⟨u30,u22,hy0L,u31,hx1L,u16,hy1L,u17,hx2L,u26,u24,u29,u20,hx3U,hy3L,u12,hx4L,hx4U,u27,hy4U,hx5L,hx5U,hy5L,hy5U,hx6L,hx6U,u13,hy6U⟩
lemma n7_root_lo_lo_1 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(603:ℝ)≤x0 ) (hx0U:x0≤(749:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(68:ℝ))
 (hx1L:(2000:ℝ)≤x1 ) (hx1U:x1≤(2343:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(209:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(550:ℝ) ) (hy2L:(1422:ℝ)≤y2 ) (hy2U:y2≤(1490:ℝ))
 (hx3L:(2657:ℝ)≤x3 ) (hx3U:x3≤(3000:ℝ) ) (hy3L:(1258:ℝ)≤y3 ) (hy3U:y3≤(1467:ℝ))
 (hx4L:(0:ℝ)≤x4 ) (hx4U:x4≤(484:ℝ) ) (hy4L:(2932:ℝ)≤y4 ) (hy4U:y4≤(3000:ℝ))
 (hx5L:(1258:ℝ)≤x5 ) (hx5U:x5≤(1742:ℝ) ) (hy5L:(2000:ℝ)≤y5 ) (hy5U:y5≤(2500:ℝ))
 (hx6L:(2516:ℝ)≤x6 ) (hx6U:x6≤(3000:ℝ) ) (hy6L:(2791:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (657:ℝ)≤x0 ∧ x0≤(738:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(39:ℝ) ∧ (2262:ℝ)≤x1 ∧ x1≤(2343:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(39:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(81:ℝ) ∧ (1428:ℝ)≤y2 ∧ y2≤(1467:ℝ) ∧ (2930:ℝ)≤x3 ∧ x3≤(3000:ℝ) ∧ (1428:ℝ)≤y3 ∧ y3≤(1467:ℝ) ∧ (307:ℝ)≤x4 ∧ x4≤(484:ℝ) ∧ (2955:ℝ)≤y4 ∧ y4≤(3000:ℝ) ∧ (1565:ℝ)≤x5 ∧ x5≤(1742:ℝ) ∧ (2000:ℝ)≤y5 ∧ y5≤(2276:ℝ) ∧ (2823:ℝ)≤x6 ∧ x6≤(3000:ℝ) ∧ (2925:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: (2197:ℝ)≤x1:=by
  have hd:(y1-y0)^2≤(209:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact hy1U
   · exact hy0L
   · exact hy0U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x0)^2+(y1-y0)^2:=by nlinarith only [hT01]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1594:ℝ) ) (D:=(209:ℝ) ) (xi:=x1 ) (xj:=x0 ) (yi:=y1 ) (yj:=y0 ) (ai:=(2000:ℝ) ) (aj:=(603:ℝ) ) (bj:=(749:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx1L) (by exact hx0U) (by exact hx0L) (by norm_num)
  linarith only [hh]
 have u1: y1≤(75:ℝ):=by
  have hd:(x1-x3)^2≤(803:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u0
   · exact hx1U
   · exact hx3L
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y3)^2+(x1-x3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1392:ℝ) ) (D:=(803:ℝ) ) (xi:=y1 ) (xj:=y3 ) (yi:=x1 ) (yj:=x3 ) (aj:=(1258:ℝ) ) (bi:=(209:ℝ) ) (bj:=(1467:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy3L) (by exact hy3U) (by norm_num)
  linarith only [hh]
 have u2: x2≤(146:ℝ):=by
  have hd:(y2-y0)^2≤(1490:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy2L
   · exact hy2U
   · exact hy0L
   · exact hy0U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x0)^2+(y2-y0)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(603:ℝ) ) (D:=(1490:ℝ) ) (xi:=x2 ) (xj:=x0 ) (yi:=y2 ) (yj:=y0 ) (aj:=(603:ℝ) ) (bi:=(550:ℝ) ) (bj:=(749:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact hx0L) (by exact hx0U) (by norm_num)
  linarith only [hh]
 have u3: y2≤(1467:ℝ):=by
  have hd:(x2-x4)^2≤(484:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u2
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y4)^2+(x2-x4)^2:=by nlinarith only [hT24]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1533:ℝ) ) (D:=(484:ℝ) ) (xi:=y2 ) (xj:=y4 ) (yi:=x2 ) (yj:=x4 ) (aj:=(2932:ℝ) ) (bi:=(1490:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact hy4L) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u4: (2854:ℝ)≤x3:=by
  have hd:(y3-y1)^2≤(1467:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact hy3U
   · exact hy1L
   · exact u1
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x1)^2+(y3-y1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(657:ℝ) ) (D:=(1467:ℝ) ) (xi:=x3 ) (xj:=x1 ) (yi:=y3 ) (yj:=y1 ) (ai:=(2657:ℝ) ) (aj:=(2197:ℝ) ) (bj:=(2343:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact hx1U) (by exact u0) (by norm_num)
  linarith only [hh]
 have u5: (1392:ℝ)≤y3:=by
  have hd:(x3-x1)^2≤(803:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u4
   · exact hx3U
   · exact u0
   · exact hx1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y1)^2+(x3-x1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1392:ℝ) ) (D:=(803:ℝ) ) (xi:=y3 ) (xj:=y1 ) (yi:=x3 ) (yj:=x1 ) (ai:=(1258:ℝ) ) (aj:=(0:ℝ) ) (bj:=(75:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3L) (by exact u1) (by exact hy1L) (by norm_num)
  linarith only [hh]
 have u6: (307:ℝ)≤x4:=by
  have hd:(y4-y2)^2≤(1578:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy4L
   · exact hy4U
   · exact hy2L
   · exact u3
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x2)^2+(y4-y2)^2:=by nlinarith only [hT24]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(307:ℝ) ) (D:=(1578:ℝ) ) (xi:=x4 ) (xj:=x2 ) (yi:=y4 ) (yj:=y2 ) (ai:=(0:ℝ) ) (aj:=(0:ℝ) ) (bj:=(146:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx4L) (by exact u2) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u7: (2955:ℝ)≤y4:=by
  have hd:(x4-x2)^2≤(484:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u6
   · exact hx4U
   · exact hx2L
   · exact u2
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y2)^2+(x4-x2)^2:=by nlinarith only [hT24]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1533:ℝ) ) (D:=(484:ℝ) ) (xi:=y4 ) (xj:=y2 ) (yi:=x4 ) (yj:=x2 ) (ai:=(2932:ℝ) ) (aj:=(1422:ℝ) ) (bj:=(1467:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact u3) (by exact hy2L) (by norm_num)
  linarith only [hh]
 have u8: (1565:ℝ)≤x5:=by
  have hd:(y5-y4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy5L
   · exact hy5U
   · exact u7
   · exact hy4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x4)^2+(y5-y4)^2:=by nlinarith only [hT45]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x5 ) (xj:=x4 ) (yi:=y5 ) (yj:=y4 ) (ai:=(1258:ℝ) ) (aj:=(307:ℝ) ) (bj:=(484:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5L) (by exact hx4U) (by exact u6) (by norm_num)
  linarith only [hh]
 have u9: y5≤(2276:ℝ):=by
  have hd:(x5-x4)^2≤(1435:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u8
   · exact hx5U
   · exact u6
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y5-y4)^2+(x5-x4)^2:=by nlinarith only [hT45]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(724:ℝ) ) (D:=(1435:ℝ) ) (xi:=y5 ) (xj:=y4 ) (yi:=x5 ) (yj:=x4 ) (aj:=(2955:ℝ) ) (bi:=(2500:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy5U) (by exact u7) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u10: (2925:ℝ)≤y6:=by
  have hd:(x6-x3)^2≤(484:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact hx6U
   · exact u4
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y3)^2+(x6-x3)^2:=by nlinarith only [hT36]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1533:ℝ) ) (D:=(484:ℝ) ) (xi:=y6 ) (xj:=y3 ) (yi:=x6 ) (yj:=x3 ) (ai:=(2791:ℝ) ) (aj:=(1392:ℝ) ) (bj:=(1467:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact hy3U) (by exact u5) (by norm_num)
  linarith only [hh]
 have u11: (2823:ℝ)≤x6:=by
  have hd:(y6-y5)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u10
   · exact hy6U
   · exact hy5L
   · exact u9
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x5)^2+(y6-y5)^2:=by nlinarith only [hT56]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x6 ) (xj:=x5 ) (yi:=y6 ) (yj:=y5 ) (ai:=(2516:ℝ) ) (aj:=(1565:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx6L) (by exact hx5U) (by exact u8) (by norm_num)
  linarith only [hh]
 have u12: x0≤(738:ℝ):=by
  have hd:(y0-y1)^2≤(75:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact hy0U
   · exact hy1L
   · exact u1
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2:=by nlinarith only [hT01]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1605:ℝ) ) (D:=(75:ℝ) ) (xi:=x0 ) (xj:=x1 ) (yi:=y0 ) (yj:=y1 ) (aj:=(2197:ℝ) ) (bi:=(749:ℝ) ) (bj:=(2343:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0U) (by exact u0) (by exact hx1U) (by norm_num)
  linarith only [hh]
 have u13: (657:ℝ)≤x0:=by
  have hd:(y0-y2)^2≤(1467:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact hy0U
   · exact hy2L
   · exact u3
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x2)^2+(y0-y2)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(657:ℝ) ) (D:=(1467:ℝ) ) (xi:=x0 ) (xj:=x2 ) (yi:=y0 ) (yj:=y2 ) (ai:=(603:ℝ) ) (aj:=(0:ℝ) ) (bj:=(146:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0L) (by exact u2) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u14: y0≤(39:ℝ):=by
  have hd:(x0-x2)^2≤(738:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u13
   · exact u12
   · exact hx2L
   · exact u2
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1428:ℝ) ) (D:=(738:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1422:ℝ) ) (bi:=(68:ℝ) ) (bj:=(1467:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy0U) (by exact hy2L) (by exact u3) (by norm_num)
  linarith only [hh]
 have u15: (2262:ℝ)≤x1:=by
  have hd:(y1-y0)^2≤(75:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact u1
   · exact hy0L
   · exact u14
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x0)^2+(y1-y0)^2:=by nlinarith only [hT01]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1605:ℝ) ) (D:=(75:ℝ) ) (xi:=x1 ) (xj:=x0 ) (yi:=y1 ) (yj:=y0 ) (ai:=(2197:ℝ) ) (aj:=(657:ℝ) ) (bj:=(738:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact u12) (by exact u13) (by norm_num)
  linarith only [hh]
 have u16: y1≤(39:ℝ):=by
  have hd:(x1-x3)^2≤(738:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u15
   · exact hx1U
   · exact u4
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y3)^2+(x1-x3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1428:ℝ) ) (D:=(738:ℝ) ) (xi:=y1 ) (xj:=y3 ) (yi:=x1 ) (yj:=x3 ) (aj:=(1392:ℝ) ) (bi:=(75:ℝ) ) (bj:=(1467:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u5) (by exact hy3U) (by norm_num)
  linarith only [hh]
 have u17: x2≤(81:ℝ):=by
  have hd:(y2-y0)^2≤(1467:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy2L
   · exact u3
   · exact hy0L
   · exact u14
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x0)^2+(y2-y0)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(657:ℝ) ) (D:=(1467:ℝ) ) (xi:=x2 ) (xj:=x0 ) (yi:=y2 ) (yj:=y0 ) (aj:=(657:ℝ) ) (bi:=(146:ℝ) ) (bj:=(738:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u2) (by exact u13) (by exact u12) (by norm_num)
  linarith only [hh]
 have u18: (1428:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(738:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u17
   · exact u13
   · exact u12
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1428:ℝ) ) (D:=(738:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1422:ℝ) ) (aj:=(0:ℝ) ) (bj:=(39:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2L) (by exact u14) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u19: (2919:ℝ)≤x3:=by
  have hd:(y3-y1)^2≤(1467:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u5
   · exact hy3U
   · exact hy1L
   · exact u16
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x1)^2+(y3-y1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(657:ℝ) ) (D:=(1467:ℝ) ) (xi:=x3 ) (xj:=x1 ) (yi:=y3 ) (yj:=y1 ) (ai:=(2854:ℝ) ) (aj:=(2262:ℝ) ) (bj:=(2343:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u4) (by exact hx1U) (by exact u15) (by norm_num)
  linarith only [hh]
 have u20: (1428:ℝ)≤y3:=by
  have hd:(x3-x1)^2≤(738:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u19
   · exact hx3U
   · exact u15
   · exact hx1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y1)^2+(x3-x1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1428:ℝ) ) (D:=(738:ℝ) ) (xi:=y3 ) (xj:=y1 ) (yi:=x3 ) (yj:=x1 ) (ai:=(1392:ℝ) ) (aj:=(0:ℝ) ) (bj:=(39:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u5) (by exact u16) (by exact hy1L) (by norm_num)
  linarith only [hh]
 have u21: (2930:ℝ)≤x3:=by
  have hd:(y3-y5)^2≤(848:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u20
   · exact hy3U
   · exact hy5L
   · exact u9
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x5)^2+(y3-y5)^2:=by nlinarith only [hT35]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1365:ℝ) ) (D:=(848:ℝ) ) (xi:=x3 ) (xj:=x5 ) (yi:=y3 ) (yj:=y5 ) (ai:=(2919:ℝ) ) (aj:=(1565:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u19) (by exact hx5U) (by exact u8) (by norm_num)
  linarith only [hh]
 exact ⟨u13,u12,hy0L,u14,u15,hx1U,hy1L,u16,hx2L,u17,u18,u3,u21,hx3U,u20,hy3U,u6,hx4U,u7,hy4U,u8,hx5U,hy5L,u9,u11,hx6U,u10,hy6U⟩
lemma n7_root_lo_hi_0 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(1000:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(306:ℝ))
 (hx1L:(2500:ℝ)≤x1 ) (hx1U:x1≤(3000:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(306:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(722:ℝ) ) (hy2L:(1258:ℝ)≤y2 ) (hy2U:y2≤(1564:ℝ))
 (hx3L:(2278:ℝ)≤x3 ) (hx3U:x3≤(3000:ℝ) ) (hy3L:(1258:ℝ)≤y3 ) (hy3U:y3≤(1564:ℝ))
 (hx4L:(0:ℝ)≤x4 ) (hx4U:x4≤(484:ℝ) ) (hy4L:(2694:ℝ)≤y4 ) (hy4U:y4≤(3000:ℝ))
 (hx5L:(1258:ℝ)≤x5 ) (hx5U:x5≤(1742:ℝ) ) (hy5L:(2000:ℝ)≤y5 ) (hy5U:y5≤(2500:ℝ))
 (hx6L:(2516:ℝ)≤x6 ) (hx6U:x6≤(3000:ℝ) ) (hy6L:(2694:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (0:ℝ)≤x0 ∧ x0≤(1000:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(306:ℝ) ∧ (2500:ℝ)≤x1 ∧ x1≤(3000:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(128:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(722:ℝ) ∧ (1258:ℝ)≤y2 ∧ y2≤(1564:ℝ) ∧ (2463:ℝ)≤x3 ∧ x3≤(3000:ℝ) ∧ (1436:ℝ)≤y3 ∧ y3≤(1485:ℝ) ∧ (0:ℝ)≤x4 ∧ x4≤(484:ℝ) ∧ (2694:ℝ)≤y4 ∧ y4≤(3000:ℝ) ∧ (1258:ℝ)≤x5 ∧ x5≤(1742:ℝ) ∧ (2000:ℝ)≤y5 ∧ y5≤(2500:ℝ) ∧ (2516:ℝ)≤x6 ∧ x6≤(3000:ℝ) ∧ (2951:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: y1≤(128:ℝ):=by
  have hd:(x1-x3)^2≤(722:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact hx1U
   · exact hx3L
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y3)^2+(x1-x3)^2:=by nlinarith only [hT13]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1436:ℝ) ) (D:=(722:ℝ) ) (xi:=y1 ) (xj:=y3 ) (yi:=x1 ) (yj:=x3 ) (aj:=(1258:ℝ) ) (bi:=(306:ℝ) ) (bj:=(1564:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy3L) (by exact hy3U) (by norm_num)
  linarith only [hh]
 have u1: (1436:ℝ)≤y3:=by
  have hd:(x3-x1)^2≤(722:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx3L
   · exact hx3U
   · exact hx1L
   · exact hx1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y1)^2+(x3-x1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1436:ℝ) ) (D:=(722:ℝ) ) (xi:=y3 ) (xj:=y1 ) (yi:=x3 ) (yj:=x1 ) (ai:=(1258:ℝ) ) (aj:=(0:ℝ) ) (bj:=(128:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3L) (by exact u0) (by exact hy1L) (by norm_num)
  linarith only [hh]
 have u2: (2463:ℝ)≤x3:=by
  have hd:(y3-y5)^2≤(1064:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u1
   · exact hy3U
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x5)^2+(y3-y5)^2:=by nlinarith only [hT35]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1205:ℝ) ) (D:=(1064:ℝ) ) (xi:=x3 ) (xj:=x5 ) (yi:=y3 ) (yj:=y5 ) (ai:=(2278:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact hx5U) (by exact hx5L) (by norm_num)
  linarith only [hh]
 have u3: y3≤(1485:ℝ):=by
  have hd:(x3-x6)^2≤(537:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u2
   · exact hx3U
   · exact hx6L
   · exact hx6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y6)^2+(x3-x6)^2:=by nlinarith only [hT36]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1515:ℝ) ) (D:=(537:ℝ) ) (xi:=y3 ) (xj:=y6 ) (yi:=x3 ) (yj:=x6 ) (aj:=(2694:ℝ) ) (bi:=(1564:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
  linarith only [hh]
 have u4: (2951:ℝ)≤y6:=by
  have hd:(x6-x3)^2≤(537:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact hx6U
   · exact u2
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y3)^2+(x6-x3)^2:=by nlinarith only [hT36]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1515:ℝ) ) (D:=(537:ℝ) ) (xi:=y6 ) (xj:=y3 ) (yi:=x6 ) (yj:=x3 ) (ai:=(2694:ℝ) ) (aj:=(1436:ℝ) ) (bj:=(1485:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact u3) (by exact u1) (by norm_num)
  linarith only [hh]
 exact ⟨hx0L,hx0U,hy0L,hy0U,hx1L,hx1U,hy1L,u0,hx2L,hx2U,hy2L,hy2U,u2,hx3U,u1,u3,hx4L,hx4U,hy4L,hy4U,hx5L,hx5U,hy5L,hy5U,hx6L,hx6U,u4,hy6U⟩
lemma n7_root_hi_0 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(1000:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(484:ℝ))
 (hx1L:(2000:ℝ)≤x1 ) (hx1U:x1≤(3000:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(484:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(1000:ℝ) ) (hy2L:(1258:ℝ)≤y2 ) (hy2U:y2≤(1742:ℝ))
 (hx3L:(2000:ℝ)≤x3 ) (hx3U:x3≤(3000:ℝ) ) (hy3L:(1258:ℝ)≤y3 ) (hy3U:y3≤(1742:ℝ))
 (hx4L:(0:ℝ)≤x4 ) (hx4U:x4≤(484:ℝ) ) (hy4L:(2516:ℝ)≤y4 ) (hy4U:y4≤(3000:ℝ))
 (hx5L:(1258:ℝ)≤x5 ) (hx5U:x5≤(1742:ℝ) ) (hy5L:(2500:ℝ)≤y5 ) (hy5U:y5≤(3000:ℝ))
 (hx6L:(2516:ℝ)≤x6 ) (hx6U:x6≤(3000:ℝ) ) (hy6L:(2516:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (0:ℝ)≤x0 ∧ x0≤(1000:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(484:ℝ) ∧ (2000:ℝ)≤x1 ∧ x1≤(3000:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(484:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(1000:ℝ) ∧ (1258:ℝ)≤y2 ∧ y2≤(1742:ℝ) ∧ (2000:ℝ)≤x3 ∧ x3≤(3000:ℝ) ∧ (1258:ℝ)≤y3 ∧ y3≤(1742:ℝ) ∧ (0:ℝ)≤x4 ∧ x4≤(215:ℝ) ∧ (2516:ℝ)≤y4 ∧ y4≤(3000:ℝ) ∧ (1527:ℝ)≤x5 ∧ x5≤(1742:ℝ) ∧ (2500:ℝ)≤y5 ∧ y5≤(3000:ℝ) ∧ (2516:ℝ)≤x6 ∧ x6≤(3000:ℝ) ∧ (2516:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: x4≤(215:ℝ):=by
  have hd:(y4-y5)^2≤(500:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy4L
   · exact hy4U
   · exact hy5L
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x5)^2+(y4-y5)^2:=by nlinarith only [hT45]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1527:ℝ) ) (D:=(500:ℝ) ) (xi:=x4 ) (xj:=x5 ) (yi:=y4 ) (yj:=y5 ) (aj:=(1258:ℝ) ) (bi:=(484:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
  linarith only [hh]
 have u1: (1527:ℝ)≤x5:=by
  have hd:(y5-y4)^2≤(500:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy5L
   · exact hy5U
   · exact hy4L
   · exact hy4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x4)^2+(y5-y4)^2:=by nlinarith only [hT45]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1527:ℝ) ) (D:=(500:ℝ) ) (xi:=x5 ) (xj:=x4 ) (yi:=y5 ) (yj:=y4 ) (ai:=(1258:ℝ) ) (aj:=(0:ℝ) ) (bj:=(215:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5L) (by exact u0) (by exact hx4L) (by norm_num)
  linarith only [hh]
 exact ⟨hx0L,hx0U,hy0L,hy0U,hx1L,hx1U,hy1L,hy1U,hx2L,hx2U,hy2L,hy2U,hx3L,hx3U,hy3L,hy3U,hx4L,u0,hy4L,hy4U,u1,hx5U,hy5L,hy5U,hx6L,hx6U,hy6L,hy6U⟩
end N7Rep14Stages
end CirclePackingConstants

namespace CirclePackingConstants
open N7Rep14Stages

end CirclePackingConstants

open CirclePackingConstants
open CirclePackingConstants.N7Rep14Stages

theorem solution (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0)(hx0U:x0≤(1000:ℝ))(hy0L:(0:ℝ)≤y0)(hy0U:y0≤(1000:ℝ))
 (hx1L:(2000:ℝ)≤x1)(hx1U:x1≤(3000:ℝ))(hy1L:(0:ℝ)≤y1)(hy1U:y1≤(1000:ℝ))
 (hx2L:(0:ℝ)≤x2)(hx2U:x2≤(1000:ℝ))(hy2L:(1000:ℝ)≤y2)(hy2U:y2≤(2000:ℝ))
 (hx3L:(2000:ℝ)≤x3)(hx3U:x3≤(3000:ℝ))(hy3L:(1000:ℝ)≤y3)(hy3U:y3≤(2000:ℝ))
 (hx4L:(0:ℝ)≤x4)(hx4U:x4≤(1000:ℝ))(hy4L:(2000:ℝ)≤y4)(hy4U:y4≤(3000:ℝ))
 (hx5L:(1000:ℝ)≤x5)(hx5U:x5≤(2000:ℝ))(hy5L:(2000:ℝ)≤y5)(hy5U:y5≤(3000:ℝ))
 (hx6L:(2000:ℝ)≤x6)(hx6U:x6≤(3000:ℝ))(hy6L:(2000:ℝ)≤y6)(hy6U:y6≤(3000:ℝ))
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
 rcases n7_root_0 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 hx0L hx0U hy0L hy0U hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
  ⟨b0_0,b0_1,b0_2,b0_3,b0_4,b0_5,b0_6,b0_7,b0_8,b0_9,b0_10,b0_11,b0_12,b0_13,b0_14,b0_15,b0_16,b0_17,b0_18,b0_19,b0_20,b0_21,b0_22,b0_23,b0_24,b0_25,b0_26,b0_27⟩
 rcases le_total y5 (2500:ℝ) with hlo | hhi
 ·
  rcases n7_root_lo_0 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 b0_0 b0_1 b0_2 b0_3 b0_4 b0_5 b0_6 b0_7 b0_8 b0_9 b0_10 b0_11 b0_12 b0_13 b0_14 b0_15 b0_16 b0_17 b0_18 b0_19 b0_20 b0_21 b0_22 hlo b0_24 b0_25 b0_26 b0_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
   ⟨b1_0,b1_1,b1_2,b1_3,b1_4,b1_5,b1_6,b1_7,b1_8,b1_9,b1_10,b1_11,b1_12,b1_13,b1_14,b1_15,b1_16,b1_17,b1_18,b1_19,b1_20,b1_21,b1_22,b1_23,b1_24,b1_25,b1_26,b1_27⟩
  rcases le_total x1 (2500:ℝ) with hlo | hhi
  ·
   rcases n7_root_lo_lo_0 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 b1_0 b1_1 b1_2 b1_3 b1_4 hlo b1_6 b1_7 b1_8 b1_9 b1_10 b1_11 b1_12 b1_13 b1_14 b1_15 b1_16 b1_17 b1_18 b1_19 b1_20 b1_21 b1_22 b1_23 b1_24 b1_25 b1_26 b1_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨b2_0,b2_1,b2_2,b2_3,b2_4,b2_5,b2_6,b2_7,b2_8,b2_9,b2_10,b2_11,b2_12,b2_13,b2_14,b2_15,b2_16,b2_17,b2_18,b2_19,b2_20,b2_21,b2_22,b2_23,b2_24,b2_25,b2_26,b2_27⟩
   rcases n7_root_lo_lo_1 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 b2_0 b2_1 b2_2 b2_3 b2_4 b2_5 b2_6 b2_7 b2_8 b2_9 b2_10 b2_11 b2_12 b2_13 b2_14 b2_15 b2_16 b2_17 b2_18 b2_19 b2_20 b2_21 b2_22 b2_23 b2_24 b2_25 b2_26 b2_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨b3_0,b3_1,b3_2,b3_3,b3_4,b3_5,b3_6,b3_7,b3_8,b3_9,b3_10,b3_11,b3_12,b3_13,b3_14,b3_15,b3_16,b3_17,b3_18,b3_19,b3_20,b3_21,b3_22,b3_23,b3_24,b3_25,b3_26,b3_27⟩
   have dx: (x3-x6)^2≤(177:ℝ)^2 := by
    apply sqdiff_bound_contract
    · exact b3_12
    · exact b3_13
    · exact b3_24
    · exact b3_25
    · norm_num
    · norm_num
   have dy: (y3-y6)^2≤(1572:ℝ)^2 := by
    apply sqdiff_bound_contract
    · exact b3_14
    · exact b3_15
    · exact b3_26
    · exact b3_27
    · norm_num
    · norm_num
   have hc: (177:ℝ)^2+(1572:ℝ)^2 < 2584683 := by norm_num
   nlinarith only [hT36,dx,dy,hc]
  ·
   rcases n7_root_lo_hi_0 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 b1_0 b1_1 b1_2 b1_3 hhi b1_5 b1_6 b1_7 b1_8 b1_9 b1_10 b1_11 b1_12 b1_13 b1_14 b1_15 b1_16 b1_17 b1_18 b1_19 b1_20 b1_21 b1_22 b1_23 b1_24 b1_25 b1_26 b1_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨b4_0,b4_1,b4_2,b4_3,b4_4,b4_5,b4_6,b4_7,b4_8,b4_9,b4_10,b4_11,b4_12,b4_13,b4_14,b4_15,b4_16,b4_17,b4_18,b4_19,b4_20,b4_21,b4_22,b4_23,b4_24,b4_25,b4_26,b4_27⟩
   have dx: (x1-x3)^2≤(537:ℝ)^2 := by
    apply sqdiff_bound_contract
    · exact b4_4
    · exact b4_5
    · exact b4_12
    · exact b4_13
    · norm_num
    · norm_num
   have dy: (y1-y3)^2≤(1485:ℝ)^2 := by
    apply sqdiff_bound_contract
    · exact b4_6
    · exact b4_7
    · exact b4_14
    · exact b4_15
    · norm_num
    · norm_num
   have hc: (537:ℝ)^2+(1485:ℝ)^2 < 2584683 := by norm_num
   nlinarith only [hT13,dx,dy,hc]
 ·
  rcases n7_root_hi_0 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 b0_0 b0_1 b0_2 b0_3 b0_4 b0_5 b0_6 b0_7 b0_8 b0_9 b0_10 b0_11 b0_12 b0_13 b0_14 b0_15 b0_16 b0_17 b0_18 b0_19 b0_20 b0_21 hhi b0_23 b0_24 b0_25 b0_26 b0_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
   ⟨b5_0,b5_1,b5_2,b5_3,b5_4,b5_5,b5_6,b5_7,b5_8,b5_9,b5_10,b5_11,b5_12,b5_13,b5_14,b5_15,b5_16,b5_17,b5_18,b5_19,b5_20,b5_21,b5_22,b5_23,b5_24,b5_25,b5_26,b5_27⟩
  have dx: (x5-x6)^2≤(1473:ℝ)^2 := by
   apply sqdiff_bound_contract
   · exact b5_20
   · exact b5_21
   · exact b5_24
   · exact b5_25
   · norm_num
   · norm_num
  have dy: (y5-y6)^2≤(500:ℝ)^2 := by
   apply sqdiff_bound_contract
   · exact b5_22
   · exact b5_23
   · exact b5_26
   · exact b5_27
   · norm_num
   · norm_num
  have hc: (1473:ℝ)^2+(500:ℝ)^2 < 2584683 := by norm_num
  nlinarith only [hT56,dx,dy,hc]
