-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_17_high_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:55:09.614054+00:00
-- url     : https://prove2.me/submissions/1452491c-e290-4b05-aa93-ffefdb2cfe35

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
namespace CirclePackingConstants
namespace N7Rep17Stages

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
 (hx3L:(1000:ℝ)≤x3 ) (hx3U:x3≤(2000:ℝ) ) (hy3L:(1000:ℝ)≤y3 ) (hy3U:y3≤(2000:ℝ))
 (hx4L:(2000:ℝ)≤x4 ) (hx4U:x4≤(3000:ℝ) ) (hy4L:(1000:ℝ)≤y4 ) (hy4U:y4≤(2000:ℝ))
 (hx5L:(0:ℝ)≤x5 ) (hx5U:x5≤(1000:ℝ) ) (hy5L:(2000:ℝ)≤y5 ) (hy5U:y5≤(3000:ℝ))
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
 : (0:ℝ)≤x0 ∧ x0≤(1000:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(484:ℝ) ∧ (2000:ℝ)≤x1 ∧ x1≤(3000:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(484:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(148:ℝ) ∧ (1258:ℝ)≤y2 ∧ y2≤(1742:ℝ) ∧ (1426:ℝ)≤x3 ∧ x3≤(1574:ℝ) ∧ (1000:ℝ)≤y3 ∧ y3≤(2000:ℝ) ∧ (2852:ℝ)≤x4 ∧ x4≤(3000:ℝ) ∧ (1258:ℝ)≤y4 ∧ y4≤(1742:ℝ) ∧ (0:ℝ)≤x5 ∧ x5≤(1000:ℝ) ∧ (2516:ℝ)≤y5 ∧ y5≤(3000:ℝ) ∧ (2000:ℝ)≤x6 ∧ x6≤(3000:ℝ) ∧ (2516:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
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
  have hd:(x1-x4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact hx1U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y1 ) (xj:=y4 ) (yi:=x1 ) (yj:=x4 ) (aj:=(1000:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(2000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy4L) (by exact hy4U) (by norm_num)
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
 have u3: x2≤(742:ℝ):=by
  have hd:(y2-y3)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u2
   · exact hy2U
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x2 ) (xj:=x3 ) (yi:=y2 ) (yj:=y3 ) (aj:=(1000:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(2000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u4: y2≤(1742:ℝ):=by
  have hd:(x2-x5)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u3
   · exact hx5L
   · exact hx5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y2 ) (xj:=y5 ) (yi:=x2 ) (yj:=x5 ) (aj:=(2000:ℝ) ) (bi:=(2000:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact hy5L) (by exact hy5U) (by norm_num)
  linarith only [hh]
 have u5: (1426:ℝ)≤x3:=by
  have hd:(y3-y2)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact hy3U
   · exact u2
   · exact u4
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x3 ) (xj:=x2 ) (yi:=y3 ) (yj:=y2 ) (ai:=(1000:ℝ) ) (aj:=(0:ℝ) ) (bj:=(742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact u3) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u6: x3≤(1742:ℝ):=by
  have hd:(y3-y4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact hy3U
   · exact hy4L
   · exact hy4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x4)^2+(y3-y4)^2:=by nlinarith only [hT34]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x3 ) (xj:=x4 ) (yi:=y3 ) (yj:=y4 ) (aj:=(2000:ℝ) ) (bi:=(2000:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3U) (by exact hx4L) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u7: (1258:ℝ)≤y4:=by
  have hd:(x4-x1)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx4L
   · exact hx4U
   · exact hx1L
   · exact hx1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y1)^2+(x4-x1)^2:=by nlinarith only [hT14]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y4 ) (xj:=y1 ) (yi:=x4 ) (yj:=x1 ) (ai:=(1000:ℝ) ) (aj:=(0:ℝ) ) (bj:=(742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact u1) (by exact hy1L) (by norm_num)
  linarith only [hh]
 have u8: (2684:ℝ)≤x4:=by
  have hd:(y4-y3)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u7
   · exact hy4U
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=x4 ) (xj:=x3 ) (yi:=y4 ) (yj:=y3 ) (ai:=(2000:ℝ) ) (aj:=(1426:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx4L) (by exact u6) (by exact u5) (by norm_num)
  linarith only [hh]
 have u9: y4≤(1742:ℝ):=by
  have hd:(x4-x6)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u8
   · exact hx4U
   · exact hx6L
   · exact hx6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y6)^2+(x4-x6)^2:=by nlinarith only [hT46]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y4 ) (xj:=y6 ) (yi:=x4 ) (yj:=x6 ) (aj:=(2000:ℝ) ) (bi:=(2000:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4U) (by exact hy6L) (by exact hy6U) (by norm_num)
  linarith only [hh]
 have u10: (2516:ℝ)≤y5:=by
  have hd:(x5-x2)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx5L
   · exact hx5U
   · exact hx2L
   · exact u3
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y5 ) (xj:=y2 ) (yi:=x5 ) (yj:=x2 ) (ai:=(2000:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy5L) (by exact u4) (by exact u2) (by norm_num)
  linarith only [hh]
 have u11: (2516:ℝ)≤y6:=by
  have hd:(x6-x4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact hx6U
   · exact u8
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y6 ) (xj:=y4 ) (yi:=x6 ) (yj:=x4 ) (ai:=(2000:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact u9) (by exact u7) (by norm_num)
  linarith only [hh]
 have u12: y0≤(484:ℝ):=by
  have hd:(x0-x2)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact hx0U
   · exact hx2L
   · exact u3
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1258:ℝ) ) (bi:=(742:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact u2) (by exact u4) (by norm_num)
  linarith only [hh]
 have u13: y1≤(484:ℝ):=by
  have hd:(x1-x4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact hx1U
   · exact u8
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y1 ) (xj:=y4 ) (yi:=x1 ) (yj:=x4 ) (aj:=(1258:ℝ) ) (bi:=(742:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u7) (by exact u9) (by norm_num)
  linarith only [hh]
 have u14: x2≤(316:ℝ):=by
  have hd:(y2-y3)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u2
   · exact u4
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x2 ) (xj:=x3 ) (yi:=y2 ) (yj:=y3 ) (aj:=(1426:ℝ) ) (bi:=(742:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u3) (by exact u5) (by exact u6) (by norm_num)
  linarith only [hh]
 have u15: x3≤(1574:ℝ):=by
  have hd:(y3-y4)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact hy3U
   · exact u7
   · exact u9
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x4)^2+(y3-y4)^2:=by nlinarith only [hT34]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x3 ) (xj:=x4 ) (yi:=y3 ) (yj:=y4 ) (aj:=(2684:ℝ) ) (bi:=(1742:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u6) (by exact u8) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u16: (2852:ℝ)≤x4:=by
  have hd:(y4-y3)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u7
   · exact u9
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x4 ) (xj:=x3 ) (yi:=y4 ) (yj:=y3 ) (ai:=(2684:ℝ) ) (aj:=(1426:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u8) (by exact u15) (by exact u5) (by norm_num)
  linarith only [hh]
 have u17: x2≤(148:ℝ):=by
  have hd:(y2-y3)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u2
   · exact u4
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x2 ) (xj:=x3 ) (yi:=y2 ) (yj:=y3 ) (aj:=(1426:ℝ) ) (bi:=(316:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u14) (by exact u5) (by exact u15) (by norm_num)
  linarith only [hh]
 exact ⟨hx0L,hx0U,hy0L,u12,hx1L,hx1U,hy1L,u13,hx2L,u17,u2,u4,u5,u15,hy3L,hy3U,u16,hx4U,u7,u9,hx5L,hx5U,u10,hy5U,hx6L,hx6U,u11,hy6U⟩
lemma n7_root_hi_0 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(1000:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(484:ℝ))
 (hx1L:(2000:ℝ)≤x1 ) (hx1U:x1≤(3000:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(484:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(148:ℝ) ) (hy2L:(1258:ℝ)≤y2 ) (hy2U:y2≤(1742:ℝ))
 (hx3L:(1426:ℝ)≤x3 ) (hx3U:x3≤(1574:ℝ) ) (hy3L:(1000:ℝ)≤y3 ) (hy3U:y3≤(2000:ℝ))
 (hx4L:(2852:ℝ)≤x4 ) (hx4U:x4≤(3000:ℝ) ) (hy4L:(1258:ℝ)≤y4 ) (hy4U:y4≤(1742:ℝ))
 (hx5L:(0:ℝ)≤x5 ) (hx5U:x5≤(1000:ℝ) ) (hy5L:(2516:ℝ)≤y5 ) (hy5U:y5≤(3000:ℝ))
 (hx6L:(2500:ℝ)≤x6 ) (hx6U:x6≤(3000:ℝ) ) (hy6L:(2516:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (0:ℝ)≤x0 ∧ x0≤(790:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(212:ℝ) ∧ (2000:ℝ)≤x1 ∧ x1≤(2345:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(210:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(83:ℝ) ∧ (1400:ℝ)≤y2 ∧ y2≤(1478:ℝ) ∧ (1491:ℝ)≤x3 ∧ x3≤(1574:ℝ) ∧ (1812:ℝ)≤y3 ∧ y3≤(2000:ℝ) ∧ (2917:ℝ)≤x4 ∧ x4≤(3000:ℝ) ∧ (1258:ℝ)≤y4 ∧ y4≤(1468:ℝ) ∧ (0:ℝ)≤x5 ∧ x5≤(516:ℝ) ∧ (2769:ℝ)≤y5 ∧ y5≤(3000:ℝ) ∧ (2541:ℝ)≤x6 ∧ x6≤(3000:ℝ) ∧ (2798:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: y4≤(1473:ℝ):=by
  have hd:(x4-x6)^2≤(500:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx4L
   · exact hx4U
   · exact hx6L
   · exact hx6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y6)^2+(x4-x6)^2:=by nlinarith only [hT46]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1527:ℝ) ) (D:=(500:ℝ) ) (xi:=y4 ) (xj:=y6 ) (yi:=x4 ) (yj:=x6 ) (aj:=(2516:ℝ) ) (bi:=(1742:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4U) (by exact hy6L) (by exact hy6U) (by norm_num)
  linarith only [hh]
 have u1: (2785:ℝ)≤y6:=by
  have hd:(x6-x4)^2≤(500:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact hx6U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1527:ℝ) ) (D:=(500:ℝ) ) (xi:=y6 ) (xj:=y4 ) (yi:=x6 ) (yj:=x4 ) (ai:=(2516:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1473:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact u0) (by exact hy4L) (by norm_num)
  linarith only [hh]
 have u2: x1≤(2356:ℝ):=by
  have hd:(y1-y4)^2≤(1473:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact hy1U
   · exact hy4L
   · exact u0
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x4)^2+(y1-y4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(644:ℝ) ) (D:=(1473:ℝ) ) (xi:=x1 ) (xj:=x4 ) (yi:=y1 ) (yj:=y4 ) (aj:=(2852:ℝ) ) (bi:=(3000:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx1U) (by exact hx4L) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u3: y1≤(215:ℝ):=by
  have hd:(x1-x4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact u2
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y1 ) (xj:=y4 ) (yi:=x1 ) (yj:=x4 ) (aj:=(1258:ℝ) ) (bi:=(484:ℝ) ) (bj:=(1473:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy4L) (by exact u0) (by norm_num)
  linarith only [hh]
 have u4: (1311:ℝ)≤y3:=by
  have hd:(x3-x1)^2≤(930:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx3L
   · exact hx3U
   · exact hx1L
   · exact u2
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y1)^2+(x3-x1)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1311:ℝ) ) (D:=(930:ℝ) ) (xi:=y3 ) (xj:=y1 ) (yi:=x3 ) (yj:=x1 ) (ai:=(1000:ℝ) ) (aj:=(0:ℝ) ) (bj:=(215:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3L) (by exact u3) (by exact hy1L) (by norm_num)
  linarith only [hh]
 have u5: (1585:ℝ)≤y3:=by
  have hd:(x3-x4)^2≤(1574:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx3L
   · exact hx3U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y4)^2+(x3-x4)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(327:ℝ) ) (D:=(1574:ℝ) ) (xi:=y3 ) (xj:=y4 ) (yi:=x3 ) (yj:=x4 ) (ai:=(1311:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1473:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u4) (by exact u0) (by exact hy4L) (by norm_num)
  linarith only [hh]
 have u6: x5≤(811:ℝ):=by
  have hd:(y5-y3)^2≤(1415:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy5L
   · exact hy5U
   · exact u5
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x3)^2+(y5-y3)^2:=by nlinarith only [hT35]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(763:ℝ) ) (D:=(1415:ℝ) ) (xi:=x5 ) (xj:=x3 ) (yi:=y5 ) (yj:=y3 ) (aj:=(1426:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5U) (by exact hx3L) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u7: x0≤(823:ℝ):=by
  have hd:(y0-y1)^2≤(484:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact hy0U
   · exact hy1L
   · exact u3
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2:=by nlinarith only [hT01]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1533:ℝ) ) (D:=(484:ℝ) ) (xi:=x0 ) (xj:=x1 ) (yi:=y0 ) (yj:=y1 ) (aj:=(2000:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(2356:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0U) (by exact hx1L) (by exact u2) (by norm_num)
  linarith only [hh]
 have u8: y0≤(361:ℝ):=by
  have hd:(x0-x2)^2≤(823:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact u7
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1381:ℝ) ) (D:=(823:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1258:ℝ) ) (bi:=(484:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
  linarith only [hh]
 have u9: (1381:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(823:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact hx2U
   · exact hx0L
   · exact u7
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1381:ℝ) ) (D:=(823:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1258:ℝ) ) (aj:=(0:ℝ) ) (bj:=(361:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2L) (by exact u8) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u10: x2≤(91:ℝ):=by
  have hd:(y2-y3)^2≤(619:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u9
   · exact hy2U
   · exact u5
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1483:ℝ) ) (D:=(619:ℝ) ) (xi:=x2 ) (xj:=x3 ) (yi:=y2 ) (yj:=y3 ) (aj:=(1426:ℝ) ) (bi:=(148:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u11: y2≤(1673:ℝ):=by
  have hd:(x2-x3)^2≤(1574:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u10
   · exact hx3L
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y3)^2+(x2-x3)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(327:ℝ) ) (D:=(1574:ℝ) ) (xi:=y2 ) (xj:=y3 ) (yi:=x2 ) (yj:=x3 ) (aj:=(1585:ℝ) ) (bi:=(1742:ℝ) ) (bj:=(2000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact u5) (by exact hy3U) (by norm_num)
  linarith only [hh]
 have u12: y2≤(1612:ℝ):=by
  have hd:(x2-x5)^2≤(811:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u10
   · exact hx5L
   · exact u6
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1388:ℝ) ) (D:=(811:ℝ) ) (xi:=y2 ) (xj:=y5 ) (yi:=x2 ) (yj:=x5 ) (aj:=(2516:ℝ) ) (bi:=(1673:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u11) (by exact hy5L) (by exact hy5U) (by norm_num)
  linarith only [hh]
 have u13: (1483:ℝ)≤x3:=by
  have hd:(y3-y2)^2≤(619:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u5
   · exact hy3U
   · exact u9
   · exact u12
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1483:ℝ) ) (D:=(619:ℝ) ) (xi:=x3 ) (xj:=x2 ) (yi:=y3 ) (yj:=y2 ) (ai:=(1426:ℝ) ) (aj:=(0:ℝ) ) (bj:=(91:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact u10) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u14: (1708:ℝ)≤y3:=by
  have hd:(x3-x2)^2≤(1574:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u13
   · exact hx3U
   · exact hx2L
   · exact u10
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y2)^2+(x3-x2)^2:=by nlinarith only [hT23]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(327:ℝ) ) (D:=(1574:ℝ) ) (xi:=y3 ) (xj:=y2 ) (yi:=x3 ) (yj:=x2 ) (ai:=(1585:ℝ) ) (aj:=(1381:ℝ) ) (bj:=(1612:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u5) (by exact u12) (by exact u9) (by norm_num)
  linarith only [hh]
 have u15: (1790:ℝ)≤y3:=by
  have hd:(x3-x4)^2≤(1517:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u13
   · exact hx3U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y4)^2+(x3-x4)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(532:ℝ) ) (D:=(1517:ℝ) ) (xi:=y3 ) (xj:=y4 ) (yi:=x3 ) (yj:=x4 ) (ai:=(1708:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1473:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u14) (by exact u0) (by exact hy4L) (by norm_num)
  linarith only [hh]
 have u16: (2909:ℝ)≤x4:=by
  have hd:(y4-y3)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy4L
   · exact u0
   · exact u15
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x4 ) (xj:=x3 ) (yi:=y4 ) (yj:=y3 ) (ai:=(2852:ℝ) ) (aj:=(1483:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx4L) (by exact hx3U) (by exact u13) (by norm_num)
  linarith only [hh]
 have u17: y4≤(1468:ℝ):=by
  have hd:(x4-x3)^2≤(1517:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u16
   · exact hx4U
   · exact u13
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y3)^2+(x4-x3)^2:=by nlinarith only [hT34]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(532:ℝ) ) (D:=(1517:ℝ) ) (xi:=y4 ) (xj:=y3 ) (yi:=x4 ) (yj:=x3 ) (aj:=(1790:ℝ) ) (bi:=(1473:ℝ) ) (bj:=(2000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact u15) (by exact hy3U) (by norm_num)
  linarith only [hh]
 have u18: (2769:ℝ)≤y5:=by
  have hd:(x5-x2)^2≤(811:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx5L
   · exact u6
   · exact hx2L
   · exact u10
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1388:ℝ) ) (D:=(811:ℝ) ) (xi:=y5 ) (xj:=y2 ) (yi:=x5 ) (yj:=x2 ) (ai:=(2516:ℝ) ) (aj:=(1381:ℝ) ) (bj:=(1612:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy5L) (by exact u12) (by exact u9) (by norm_num)
  linarith only [hh]
 have u19: x5≤(516:ℝ):=by
  have hd:(y5-y3)^2≤(1210:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u18
   · exact hy5U
   · exact u15
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x3)^2+(y5-y3)^2:=by nlinarith only [hT35]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1058:ℝ) ) (D:=(1210:ℝ) ) (xi:=x5 ) (xj:=x3 ) (yi:=y5 ) (yj:=y3 ) (aj:=(1483:ℝ) ) (bi:=(811:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u6) (by exact u13) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u20: (2541:ℝ)≤x6:=by
  have hd:(y6-y3)^2≤(1210:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u1
   · exact hy6U
   · exact u15
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x3)^2+(y6-y3)^2:=by nlinarith only [hT36]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1058:ℝ) ) (D:=(1210:ℝ) ) (xi:=x6 ) (xj:=x3 ) (yi:=y6 ) (yj:=y3 ) (ai:=(2500:ℝ) ) (aj:=(1483:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx6L) (by exact hx3U) (by exact u13) (by norm_num)
  linarith only [hh]
 have u21: (2798:ℝ)≤y6:=by
  have hd:(x6-x4)^2≤(459:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u20
   · exact hx6U
   · exact u16
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1540:ℝ) ) (D:=(459:ℝ) ) (xi:=y6 ) (xj:=y4 ) (yi:=x6 ) (yj:=x4 ) (ai:=(2785:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1468:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u17) (by exact hy4L) (by norm_num)
  linarith only [hh]
 have u22: x0≤(790:ℝ):=by
  have hd:(y0-y1)^2≤(361:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact u8
   · exact hy1L
   · exact u3
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2:=by nlinarith only [hT01]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1566:ℝ) ) (D:=(361:ℝ) ) (xi:=x0 ) (xj:=x1 ) (yi:=y0 ) (yj:=y1 ) (aj:=(2000:ℝ) ) (bi:=(823:ℝ) ) (bj:=(2356:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u7) (by exact hx1L) (by exact u2) (by norm_num)
  linarith only [hh]
 have u23: y0≤(212:ℝ):=by
  have hd:(x0-x2)^2≤(790:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact u22
   · exact hx2L
   · exact u10
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1400:ℝ) ) (D:=(790:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1381:ℝ) ) (bi:=(361:ℝ) ) (bj:=(1612:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u8) (by exact u9) (by exact u12) (by norm_num)
  linarith only [hh]
 have u24: x1≤(2345:ℝ):=by
  have hd:(y1-y4)^2≤(1468:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact u3
   · exact hy4L
   · exact u17
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x4)^2+(y1-y4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(655:ℝ) ) (D:=(1468:ℝ) ) (xi:=x1 ) (xj:=x4 ) (yi:=y1 ) (yj:=y4 ) (aj:=(2909:ℝ) ) (bi:=(2356:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u2) (by exact u16) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u25: y1≤(210:ℝ):=by
  have hd:(x1-x4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact u24
   · exact u16
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y1 ) (xj:=y4 ) (yi:=x1 ) (yj:=x4 ) (aj:=(1258:ℝ) ) (bi:=(215:ℝ) ) (bj:=(1468:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u3) (by exact hy4L) (by exact u17) (by norm_num)
  linarith only [hh]
 have u26: (1400:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(790:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u10
   · exact hx0L
   · exact u22
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1400:ℝ) ) (D:=(790:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1381:ℝ) ) (aj:=(0:ℝ) ) (bj:=(212:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u9) (by exact u23) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u27: x2≤(83:ℝ):=by
  have hd:(y2-y3)^2≤(600:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u26
   · exact u12
   · exact u15
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1491:ℝ) ) (D:=(600:ℝ) ) (xi:=x2 ) (xj:=x3 ) (yi:=y2 ) (yj:=y3 ) (aj:=(1483:ℝ) ) (bi:=(91:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u10) (by exact u13) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u28: y2≤(1478:ℝ):=by
  have hd:(x2-x5)^2≤(516:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u27
   · exact hx5L
   · exact u19
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1522:ℝ) ) (D:=(516:ℝ) ) (xi:=y2 ) (xj:=y5 ) (yi:=x2 ) (yj:=x5 ) (aj:=(2769:ℝ) ) (bi:=(1612:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u12) (by exact u18) (by exact hy5U) (by norm_num)
  linarith only [hh]
 have u29: (1491:ℝ)≤x3:=by
  have hd:(y3-y2)^2≤(600:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u15
   · exact hy3U
   · exact u26
   · exact u28
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1491:ℝ) ) (D:=(600:ℝ) ) (xi:=x3 ) (xj:=x2 ) (yi:=y3 ) (yj:=y2 ) (ai:=(1483:ℝ) ) (aj:=(0:ℝ) ) (bj:=(83:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u13) (by exact u27) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u30: (1812:ℝ)≤y3:=by
  have hd:(x3-x4)^2≤(1509:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u29
   · exact hx3U
   · exact u16
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y4)^2+(x3-x4)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(554:ℝ) ) (D:=(1509:ℝ) ) (xi:=y3 ) (xj:=y4 ) (yi:=x3 ) (yj:=x4 ) (ai:=(1790:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1468:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u15) (by exact u17) (by exact hy4L) (by norm_num)
  linarith only [hh]
 have u31: (2917:ℝ)≤x4:=by
  have hd:(y4-y3)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy4L
   · exact u17
   · exact u30
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x4 ) (xj:=x3 ) (yi:=y4 ) (yj:=y3 ) (ai:=(2909:ℝ) ) (aj:=(1491:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u16) (by exact hx3U) (by exact u29) (by norm_num)
  linarith only [hh]
 exact ⟨hx0L,u22,hy0L,u23,hx1L,u24,hy1L,u25,hx2L,u27,u26,u28,u29,hx3U,u30,hy3U,u31,hx4U,hy4L,u17,hx5L,u19,u18,hy5U,u20,hx6U,u21,hy6U⟩
lemma n7_root_hi_1 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(790:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(212:ℝ))
 (hx1L:(2000:ℝ)≤x1 ) (hx1U:x1≤(2345:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(210:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(83:ℝ) ) (hy2L:(1400:ℝ)≤y2 ) (hy2U:y2≤(1478:ℝ))
 (hx3L:(1491:ℝ)≤x3 ) (hx3U:x3≤(1574:ℝ) ) (hy3L:(1812:ℝ)≤y3 ) (hy3U:y3≤(2000:ℝ))
 (hx4L:(2917:ℝ)≤x4 ) (hx4U:x4≤(3000:ℝ) ) (hy4L:(1258:ℝ)≤y4 ) (hy4U:y4≤(1468:ℝ))
 (hx5L:(0:ℝ)≤x5 ) (hx5U:x5≤(516:ℝ) ) (hy5L:(2769:ℝ)≤y5 ) (hy5U:y5≤(3000:ℝ))
 (hx6L:(2541:ℝ)≤x6 ) (hx6U:x6≤(3000:ℝ) ) (hy6L:(2798:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (650:ℝ)≤x0 ∧ x0≤(692:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(19:ℝ) ∧ (2257:ℝ)≤x1 ∧ x1≤(2298:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(38:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(75:ℝ) ∧ (1420:ℝ)≤y2 ∧ y2≤(1470:ℝ) ∧ (1499:ℝ)≤x3 ∧ x3≤(1574:ℝ) ∧ (1833:ℝ)≤y3 ∧ y3≤(2000:ℝ) ∧ (2993:ℝ)≤x4 ∧ x4≤(3000:ℝ) ∧ (1408:ℝ)≤y4 ∧ y4≤(1425:ℝ) ∧ (297:ℝ)≤x5 ∧ x5≤(469:ℝ) ∧ (2950:ℝ)≤y5 ∧ y5≤(3000:ℝ) ∧ (2604:ℝ)≤x6 ∧ x6≤(2776:ℝ) ∧ (2966:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: y4≤(1446:ℝ):=by
  have hd:(x4-x3)^2≤(1509:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx4L
   · exact hx4U
   · exact hx3L
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y3)^2+(x4-x3)^2:=by nlinarith only [hT34]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(554:ℝ) ) (D:=(1509:ℝ) ) (xi:=y4 ) (xj:=y3 ) (yi:=x4 ) (yj:=x3 ) (aj:=(1812:ℝ) ) (bi:=(1468:ℝ) ) (bj:=(2000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4U) (by exact hy3L) (by exact hy3U) (by norm_num)
  linarith only [hh]
 have u1: (157:ℝ)≤x5:=by
  have hd:(y5-y2)^2≤(1600:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy5L
   · exact hy5U
   · exact hy2L
   · exact hy2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x2)^2+(y5-y2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(157:ℝ) ) (D:=(1600:ℝ) ) (xi:=x5 ) (xj:=x2 ) (yi:=y5 ) (yj:=y2 ) (ai:=(0:ℝ) ) (aj:=(0:ℝ) ) (bj:=(83:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5L) (by exact hx2U) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u2: (2922:ℝ)≤y5:=by
  have hd:(x5-x2)^2≤(516:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u1
   · exact hx5U
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1522:ℝ) ) (D:=(516:ℝ) ) (xi:=y5 ) (xj:=y2 ) (yi:=x5 ) (yj:=x2 ) (ai:=(2769:ℝ) ) (aj:=(1400:ℝ) ) (bj:=(1478:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy5L) (by exact hy2U) (by exact hy2L) (by norm_num)
  linarith only [hh]
 have u3: x5≤(491:ℝ):=by
  have hd:(y5-y3)^2≤(1188:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u2
   · exact hy5U
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x3)^2+(y5-y3)^2:=by nlinarith only [hT35]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1083:ℝ) ) (D:=(1188:ℝ) ) (xi:=x5 ) (xj:=x3 ) (yi:=y5 ) (yj:=y3 ) (aj:=(1491:ℝ) ) (bi:=(516:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5U) (by exact hx3L) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u4: (2574:ℝ)≤x6:=by
  have hd:(y6-y3)^2≤(1188:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy6L
   · exact hy6U
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x3)^2+(y6-y3)^2:=by nlinarith only [hT36]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1083:ℝ) ) (D:=(1188:ℝ) ) (xi:=x6 ) (xj:=x3 ) (yi:=y6 ) (yj:=y3 ) (ai:=(2541:ℝ) ) (aj:=(1491:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx6L) (by exact hx3U) (by exact hx3L) (by norm_num)
  linarith only [hh]
 have u5: (2808:ℝ)≤y6:=by
  have hd:(x6-x4)^2≤(426:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u4
   · exact hx6U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1550:ℝ) ) (D:=(426:ℝ) ) (xi:=y6 ) (xj:=y4 ) (yi:=x6 ) (yj:=x4 ) (ai:=(2798:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1446:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact u0) (by exact hy4L) (by norm_num)
  linarith only [hh]
 have u6: x0≤(752:ℝ):=by
  have hd:(y0-y1)^2≤(212:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact hy0U
   · exact hy1L
   · exact hy1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2:=by nlinarith only [hT01]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1593:ℝ) ) (D:=(212:ℝ) ) (xi:=x0 ) (xj:=x1 ) (yi:=y0 ) (yj:=y1 ) (aj:=(2000:ℝ) ) (bi:=(790:ℝ) ) (bj:=(2345:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0U) (by exact hx1L) (by exact hx1U) (by norm_num)
  linarith only [hh]
 have u7: (632:ℝ)≤x0:=by
  have hd:(y0-y2)^2≤(1478:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact hy0U
   · exact hy2L
   · exact hy2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x2)^2+(y0-y2)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(632:ℝ) ) (D:=(1478:ℝ) ) (xi:=x0 ) (xj:=x2 ) (yi:=y0 ) (yj:=y2 ) (ai:=(0:ℝ) ) (aj:=(0:ℝ) ) (bj:=(83:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0L) (by exact hx2U) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u8: y0≤(58:ℝ):=by
  have hd:(x0-x2)^2≤(752:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u7
   · exact u6
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1420:ℝ) ) (D:=(752:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1400:ℝ) ) (bi:=(212:ℝ) ) (bj:=(1478:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
  linarith only [hh]
 have u9: (2225:ℝ)≤x1:=by
  have hd:(y1-y0)^2≤(210:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact hy1U
   · exact hy0L
   · exact u8
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x0)^2+(y1-y0)^2:=by nlinarith only [hT01]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1593:ℝ) ) (D:=(210:ℝ) ) (xi:=x1 ) (xj:=x0 ) (yi:=y1 ) (yj:=y0 ) (ai:=(2000:ℝ) ) (aj:=(632:ℝ) ) (bj:=(752:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx1L) (by exact u6) (by exact u7) (by norm_num)
  linarith only [hh]
 have u10: x1≤(2298:ℝ):=by
  have hd:(y1-y4)^2≤(1446:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact hy1U
   · exact hy4L
   · exact u0
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x4)^2+(y1-y4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(702:ℝ) ) (D:=(1446:ℝ) ) (xi:=x1 ) (xj:=x4 ) (yi:=y1 ) (yj:=y4 ) (aj:=(2917:ℝ) ) (bi:=(2345:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx1U) (by exact hx4L) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u11: y1≤(38:ℝ):=by
  have hd:(x1-x4)^2≤(775:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u9
   · exact u10
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1408:ℝ) ) (D:=(775:ℝ) ) (xi:=y1 ) (xj:=y4 ) (yi:=x1 ) (yj:=x4 ) (aj:=(1258:ℝ) ) (bi:=(210:ℝ) ) (bj:=(1446:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy4L) (by exact u0) (by norm_num)
  linarith only [hh]
 have u12: (1420:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(752:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact hx2U
   · exact u7
   · exact u6
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1420:ℝ) ) (D:=(752:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1400:ℝ) ) (aj:=(0:ℝ) ) (bj:=(58:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2L) (by exact u8) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u13: x2≤(75:ℝ):=by
  have hd:(y2-y3)^2≤(580:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u12
   · exact hy2U
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1499:ℝ) ) (D:=(580:ℝ) ) (xi:=x2 ) (xj:=x3 ) (yi:=y2 ) (yj:=y3 ) (aj:=(1491:ℝ) ) (bi:=(83:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u14: y2≤(1470:ℝ):=by
  have hd:(x2-x5)^2≤(491:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u13
   · exact u1
   · exact u3
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1530:ℝ) ) (D:=(491:ℝ) ) (xi:=y2 ) (xj:=y5 ) (yi:=x2 ) (yj:=x5 ) (aj:=(2922:ℝ) ) (bi:=(1478:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact u2) (by exact hy5U) (by norm_num)
  linarith only [hh]
 have u15: (1499:ℝ)≤x3:=by
  have hd:(y3-y2)^2≤(580:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact hy3U
   · exact u12
   · exact u14
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1499:ℝ) ) (D:=(580:ℝ) ) (xi:=x3 ) (xj:=x2 ) (yi:=y3 ) (yj:=y2 ) (ai:=(1491:ℝ) ) (aj:=(0:ℝ) ) (bj:=(75:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact u13) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u16: (1833:ℝ)≤y3:=by
  have hd:(x3-x4)^2≤(1501:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u15
   · exact hx3U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y4)^2+(x3-x4)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(575:ℝ) ) (D:=(1501:ℝ) ) (xi:=y3 ) (xj:=y4 ) (yi:=x3 ) (yj:=x4 ) (ai:=(1812:ℝ) ) (aj:=(1258:ℝ) ) (bj:=(1446:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3L) (by exact u0) (by exact hy4L) (by norm_num)
  linarith only [hh]
 have u17: (2927:ℝ)≤x4:=by
  have hd:(y4-y1)^2≤(1446:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy4L
   · exact u0
   · exact hy1L
   · exact u11
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x1)^2+(y4-y1)^2:=by nlinarith only [hT14]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(702:ℝ) ) (D:=(1446:ℝ) ) (xi:=x4 ) (xj:=x1 ) (yi:=y4 ) (yj:=y1 ) (ai:=(2917:ℝ) ) (aj:=(2225:ℝ) ) (bj:=(2298:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx4L) (by exact u10) (by exact u9) (by norm_num)
  linarith only [hh]
 have u18: (1408:ℝ)≤y4:=by
  have hd:(x4-x1)^2≤(775:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u17
   · exact hx4U
   · exact u9
   · exact u10
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y1)^2+(x4-x1)^2:=by nlinarith only [hT14]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1408:ℝ) ) (D:=(775:ℝ) ) (xi:=y4 ) (xj:=y1 ) (yi:=x4 ) (yj:=x1 ) (ai:=(1258:ℝ) ) (aj:=(0:ℝ) ) (bj:=(38:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact u11) (by exact hy1L) (by norm_num)
  linarith only [hh]
 have u19: (2993:ℝ)≤x4:=by
  have hd:(y4-y3)^2≤(592:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u18
   · exact u0
   · exact u16
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1494:ℝ) ) (D:=(592:ℝ) ) (xi:=x4 ) (xj:=x3 ) (yi:=y4 ) (yj:=y3 ) (ai:=(2927:ℝ) ) (aj:=(1499:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u17) (by exact hx3U) (by exact u15) (by norm_num)
  linarith only [hh]
 have u20: y4≤(1425:ℝ):=by
  have hd:(x4-x3)^2≤(1501:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u19
   · exact hx4U
   · exact u15
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y3)^2+(x4-x3)^2:=by nlinarith only [hT34]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(575:ℝ) ) (D:=(1501:ℝ) ) (xi:=y4 ) (xj:=y3 ) (yi:=x4 ) (yj:=x3 ) (aj:=(1833:ℝ) ) (bi:=(1446:ℝ) ) (bj:=(2000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact u16) (by exact hy3U) (by norm_num)
  linarith only [hh]
 have u21: (297:ℝ)≤x5:=by
  have hd:(y5-y2)^2≤(1580:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u2
   · exact hy5U
   · exact u12
   · exact u14
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x2)^2+(y5-y2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(297:ℝ) ) (D:=(1580:ℝ) ) (xi:=x5 ) (xj:=x2 ) (yi:=y5 ) (yj:=y2 ) (ai:=(157:ℝ) ) (aj:=(0:ℝ) ) (bj:=(75:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u13) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u22: (2950:ℝ)≤y5:=by
  have hd:(x5-x2)^2≤(491:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u21
   · exact u3
   · exact hx2L
   · exact u13
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1530:ℝ) ) (D:=(491:ℝ) ) (xi:=y5 ) (xj:=y2 ) (yi:=x5 ) (yj:=x2 ) (ai:=(2922:ℝ) ) (aj:=(1420:ℝ) ) (bj:=(1470:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u2) (by exact u14) (by exact u12) (by norm_num)
  linarith only [hh]
 have u23: x5≤(469:ℝ):=by
  have hd:(y5-y3)^2≤(1167:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u22
   · exact hy5U
   · exact u16
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x3)^2+(y5-y3)^2:=by nlinarith only [hT35]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1105:ℝ) ) (D:=(1167:ℝ) ) (xi:=x5 ) (xj:=x3 ) (yi:=y5 ) (yj:=y3 ) (aj:=(1499:ℝ) ) (bi:=(491:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u3) (by exact u15) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u24: (2604:ℝ)≤x6:=by
  have hd:(y6-y3)^2≤(1167:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u5
   · exact hy6U
   · exact u16
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x3)^2+(y6-y3)^2:=by nlinarith only [hT36]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1105:ℝ) ) (D:=(1167:ℝ) ) (xi:=x6 ) (xj:=x3 ) (yi:=y6 ) (yj:=y3 ) (ai:=(2574:ℝ) ) (aj:=(1499:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u4) (by exact hx3U) (by exact u15) (by norm_num)
  linarith only [hh]
 have u25: x6≤(2776:ℝ):=by
  have hd:(y6-y4)^2≤(1592:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u5
   · exact hy6U
   · exact u18
   · exact u20
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x4)^2+(y6-y4)^2:=by nlinarith only [hT46]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(224:ℝ) ) (D:=(1592:ℝ) ) (xi:=x6 ) (xj:=x4 ) (yi:=y6 ) (yj:=y4 ) (aj:=(2993:ℝ) ) (bi:=(3000:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx6U) (by exact u19) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u26: (2966:ℝ)≤y6:=by
  have hd:(x6-x4)^2≤(396:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u24
   · exact u25
   · exact u19
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1558:ℝ) ) (D:=(396:ℝ) ) (xi:=y6 ) (xj:=y4 ) (yi:=x6 ) (yj:=x4 ) (ai:=(2808:ℝ) ) (aj:=(1408:ℝ) ) (bj:=(1425:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u5) (by exact u20) (by exact u18) (by norm_num)
  linarith only [hh]
 have u27: x0≤(692:ℝ):=by
  have hd:(y0-y1)^2≤(58:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact u8
   · exact hy1L
   · exact u11
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2:=by nlinarith only [hT01]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1606:ℝ) ) (D:=(58:ℝ) ) (xi:=x0 ) (xj:=x1 ) (yi:=y0 ) (yj:=y1 ) (aj:=(2225:ℝ) ) (bi:=(752:ℝ) ) (bj:=(2298:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u6) (by exact u9) (by exact u10) (by norm_num)
  linarith only [hh]
 have u28: (650:ℝ)≤x0:=by
  have hd:(y0-y2)^2≤(1470:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact u8
   · exact u12
   · exact u14
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x2)^2+(y0-y2)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(650:ℝ) ) (D:=(1470:ℝ) ) (xi:=x0 ) (xj:=x2 ) (yi:=y0 ) (yj:=y2 ) (ai:=(632:ℝ) ) (aj:=(0:ℝ) ) (bj:=(75:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u7) (by exact u13) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u29: y0≤(19:ℝ):=by
  have hd:(x0-x2)^2≤(692:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u28
   · exact u27
   · exact hx2L
   · exact u13
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1451:ℝ) ) (D:=(692:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1420:ℝ) ) (bi:=(58:ℝ) ) (bj:=(1470:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u8) (by exact u12) (by exact u14) (by norm_num)
  linarith only [hh]
 have u30: (2257:ℝ)≤x1:=by
  have hd:(y1-y0)^2≤(38:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact u11
   · exact hy0L
   · exact u29
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x0)^2+(y1-y0)^2:=by nlinarith only [hT01]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1607:ℝ) ) (D:=(38:ℝ) ) (xi:=x1 ) (xj:=x0 ) (yi:=y1 ) (yj:=y0 ) (ai:=(2225:ℝ) ) (aj:=(650:ℝ) ) (bj:=(692:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u9) (by exact u27) (by exact u28) (by norm_num)
  linarith only [hh]
 exact ⟨u28,u27,hy0L,u29,u30,u10,hy1L,u11,hx2L,u13,u12,u14,u15,hx3U,u16,hy3U,u19,hx4U,u18,u20,u21,u23,u22,hy5U,u24,u25,u26,hy6U⟩
end N7Rep17Stages
end CirclePackingConstants
open CirclePackingConstants.N7Rep17Stages

theorem solution (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L:(0:ℝ)≤x0) (hx0U:x0≤(1000:ℝ)) (hy0L:(0:ℝ)≤y0) (hy0U:y0≤(1000:ℝ))
  (hx1L:(2000:ℝ)≤x1) (hx1U:x1≤(3000:ℝ)) (hy1L:(0:ℝ)≤y1) (hy1U:y1≤(1000:ℝ))
  (hx2L:(0:ℝ)≤x2) (hx2U:x2≤(1000:ℝ)) (hy2L:(1000:ℝ)≤y2) (hy2U:y2≤(2000:ℝ))
  (hx3L:(1000:ℝ)≤x3) (hx3U:x3≤(2000:ℝ)) (hy3L:(1000:ℝ)≤y3) (hy3U:y3≤(2000:ℝ))
  (hx4L:(2000:ℝ)≤x4) (hx4U:x4≤(3000:ℝ)) (hy4L:(1000:ℝ)≤y4) (hy4U:y4≤(2000:ℝ))
  (hx5L:(0:ℝ)≤x5) (hx5U:x5≤(1000:ℝ)) (hy5L:(2000:ℝ)≤y5) (hy5U:y5≤(3000:ℝ))
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
  (hsplit0 : (2500:ℝ) ≤ x6)
  : False := by
  rcases n7_root_0 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 hx0L hx0U hy0L hy0U hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
  ⟨b0_0,b0_1,b0_2,b0_3,b0_4,b0_5,b0_6,b0_7,b0_8,b0_9,b0_10,b0_11,b0_12,b0_13,b0_14,b0_15,b0_16,b0_17,b0_18,b0_19,b0_20,b0_21,b0_22,b0_23,b0_24,b0_25,b0_26,b0_27⟩
  rcases n7_root_hi_0 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 b0_0 b0_1 b0_2 b0_3 b0_4 b0_5 b0_6 b0_7 b0_8 b0_9 b0_10 b0_11 b0_12 b0_13 b0_14 b0_15 b0_16 b0_17 b0_18 b0_19 b0_20 b0_21 b0_22 b0_23 hsplit0 b0_25 b0_26 b0_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
  ⟨b5_0,b5_1,b5_2,b5_3,b5_4,b5_5,b5_6,b5_7,b5_8,b5_9,b5_10,b5_11,b5_12,b5_13,b5_14,b5_15,b5_16,b5_17,b5_18,b5_19,b5_20,b5_21,b5_22,b5_23,b5_24,b5_25,b5_26,b5_27⟩
  rcases n7_root_hi_1 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 b5_0 b5_1 b5_2 b5_3 b5_4 b5_5 b5_6 b5_7 b5_8 b5_9 b5_10 b5_11 b5_12 b5_13 b5_14 b5_15 b5_16 b5_17 b5_18 b5_19 b5_20 b5_21 b5_22 b5_23 b5_24 b5_25 b5_26 b5_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
  ⟨b6_0,b6_1,b6_2,b6_3,b6_4,b6_5,b6_6,b6_7,b6_8,b6_9,b6_10,b6_11,b6_12,b6_13,b6_14,b6_15,b6_16,b6_17,b6_18,b6_19,b6_20,b6_21,b6_22,b6_23,b6_24,b6_25,b6_26,b6_27⟩
  have dx : (x1-x4)^2 ≤ (743:ℝ)^2 := by
    apply sqdiff_bound_contract
    · exact b6_4
    · exact b6_5
    · exact b6_16
    · exact b6_17
    · norm_num
    · norm_num
  have dy : (y1-y4)^2 ≤ (1425:ℝ)^2 := by
    apply sqdiff_bound_contract
    · exact b6_6
    · exact b6_7
    · exact b6_18
    · exact b6_19
    · norm_num
    · norm_num
  have hc : (743:ℝ)^2 + (1425:ℝ)^2 < 2584683 := by norm_num
  nlinarith only [hT14, dx, dy, hc]
