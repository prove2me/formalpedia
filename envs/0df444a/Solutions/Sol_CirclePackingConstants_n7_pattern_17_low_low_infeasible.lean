-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_17_low_low_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:08:13.549988+00:00
-- url     : https://prove2.me/submissions/dec16758-a851-4f9d-a45e-ea791c1a3c62

import Mathlib.Data.Real.Sqrt
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
  (hsplit0 : x6 ≤ (2500:ℝ))
  (hsplit1 : x1 ≤ (2500:ℝ))
  : False := by
  have u0:y0≤(742:ℝ):=by
    have hd:(x0-x2)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact hx0U
      · exact hx2L
      · exact hx2U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y0) (xj:=y2) (yi:=x0) (yj:=x2) (aj:=(1000:ℝ)) (bi:=(1000:ℝ)) (bj:=(2000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
    linarith only [hh]
  have u1:y1≤(742:ℝ):=by
    have hd:(x1-x4)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact hx1U
      · exact hx4L
      · exact hx4U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y1) (xj:=y4) (yi:=x1) (yj:=x4) (aj:=(1000:ℝ)) (bi:=(1000:ℝ)) (bj:=(2000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy4L) (by exact hy4U) (by norm_num)
    linarith only [hh]
  have u2:(1258:ℝ)≤y2:=by
    have hd:(x2-x0)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact hx2U
      · exact hx0L
      · exact hx0U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y2) (xj:=y0) (yi:=x2) (yj:=x0) (ai:=(1000:ℝ)) (aj:=(0:ℝ)) (bj:=(742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy2L) (by exact u0) (by exact hy0L) (by norm_num)
    linarith only [hh]
  have u3:x2≤(742:ℝ):=by
    have hd:(y2-y3)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u2
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=x2) (xj:=x3) (yi:=y2) (yj:=y3) (aj:=(1000:ℝ)) (bi:=(1000:ℝ)) (bj:=(2000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u4:y2≤(1742:ℝ):=by
    have hd:(x2-x5)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u3
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y2) (xj:=y5) (yi:=x2) (yj:=x5) (aj:=(2000:ℝ)) (bi:=(2000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u5:(1426:ℝ)≤x3:=by
    have hd:(y3-y2)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact u2
      · exact u4
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=x3) (xj:=x2) (yi:=y3) (yj:=y2) (ai:=(1000:ℝ)) (aj:=(0:ℝ)) (bj:=(742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact u3) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have u6:x3≤(1742:ℝ):=by
    have hd:(y3-y4)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact hy4L
      · exact hy4U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x3-x4)^2+(y3-y4)^2:=by nlinarith only [hT34]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=x3) (xj:=x4) (yi:=y3) (yj:=y4) (aj:=(2000:ℝ)) (bi:=(2000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx3U) (by exact hx4L) (by exact hx4U) (by norm_num)
    linarith only [hh]
  have u7:(1258:ℝ)≤y4:=by
    have hd:(x4-x1)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact hx4U
      · exact hx1L
      · exact hx1U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y4-y1)^2+(x4-x1)^2:=by nlinarith only [hT14]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y4) (xj:=y1) (yi:=x4) (yj:=x1) (ai:=(1000:ℝ)) (aj:=(0:ℝ)) (bj:=(742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact u1) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u8:(2684:ℝ)≤x4:=by
    have hd:(y4-y3)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u7
      · exact hy4U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=x4) (xj:=x3) (yi:=y4) (yj:=y3) (ai:=(2000:ℝ)) (aj:=(1426:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx4L) (by exact u6) (by exact u5) (by norm_num)
    linarith only [hh]
  have u9:y4≤(1742:ℝ):=by
    have hd:(x4-x6)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u8
      · exact hx4U
      · exact hx6L
      · exact hx6U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y4-y6)^2+(x4-x6)^2:=by nlinarith only [hT46]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y4) (xj:=y6) (yi:=x4) (yj:=x6) (aj:=(2000:ℝ)) (bi:=(2000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy4U) (by exact hy6L) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u10:(2516:ℝ)≤y5:=by
    have hd:(x5-x2)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact hx2L
      · exact u3
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y5) (xj:=y2) (yi:=x5) (yj:=x2) (ai:=(2000:ℝ)) (aj:=(1258:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy5L) (by exact u4) (by exact u2) (by norm_num)
    linarith only [hh]
  have u11:(2516:ℝ)≤y6:=by
    have hd:(x6-x4)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact u8
      · exact hx4U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y6) (xj:=y4) (yi:=x6) (yj:=x4) (ai:=(2000:ℝ)) (aj:=(1258:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact u9) (by exact u7) (by norm_num)
    linarith only [hh]
  have u12:y0≤(484:ℝ):=by
    have hd:(x0-x2)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact hx0U
      · exact hx2L
      · exact u3
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y0) (xj:=y2) (yi:=x0) (yj:=x2) (aj:=(1258:ℝ)) (bi:=(742:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact u2) (by exact u4) (by norm_num)
    linarith only [hh]
  have u13:y1≤(484:ℝ):=by
    have hd:(x1-x4)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact hx1U
      · exact u8
      · exact hx4U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y1) (xj:=y4) (yi:=x1) (yj:=x4) (aj:=(1258:ℝ)) (bi:=(742:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u7) (by exact u9) (by norm_num)
    linarith only [hh]
  have u14:x2≤(316:ℝ):=by
    have hd:(y2-y3)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u2
      · exact u4
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=x2) (xj:=x3) (yi:=y2) (yj:=y3) (aj:=(1426:ℝ)) (bi:=(742:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u3) (by exact u5) (by exact u6) (by norm_num)
    linarith only [hh]
  have u15:x3≤(1574:ℝ):=by
    have hd:(y3-y4)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact u7
      · exact u9
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x3-x4)^2+(y3-y4)^2:=by nlinarith only [hT34]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=x3) (xj:=x4) (yi:=y3) (yj:=y4) (aj:=(2684:ℝ)) (bi:=(1742:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u6) (by exact u8) (by exact hx4U) (by norm_num)
    linarith only [hh]
  have u16:(2852:ℝ)≤x4:=by
    have hd:(y4-y3)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u7
      · exact u9
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=x4) (xj:=x3) (yi:=y4) (yj:=y3) (ai:=(2684:ℝ)) (aj:=(1426:ℝ)) (bj:=(1574:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u8) (by exact u15) (by exact u5) (by norm_num)
    linarith only [hh]
  have u17:x2≤(148:ℝ):=by
    have hd:(y2-y3)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u2
      · exact u4
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=x2) (xj:=x3) (yi:=y2) (yj:=y3) (aj:=(1426:ℝ)) (bi:=(316:ℝ)) (bj:=(1574:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u14) (by exact u5) (by exact u15) (by norm_num)
    linarith only [hh]
  have u18:y3≤(1804:ℝ):=by
    have hd:(x3-x6)^2≤(1074:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u5
      · exact u15
      · exact hx6L
      · exact hsplit0
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y3-y6)^2+(x3-x6)^2:=by nlinarith only [hT36]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1196:ℝ)) (D:=(1074:ℝ)) (xi:=y3) (xj:=y6) (yi:=x3) (yj:=x6) (aj:=(2516:ℝ)) (bi:=(2000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy3U) (by exact u11) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u19:x5≤(967:ℝ):=by
    have hd:(y5-y6)^2≤(484:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u10
      · exact hy5U
      · exact u11
      · exact hy6U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x5-x6)^2+(y5-y6)^2:=by nlinarith only [hT56]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1533:ℝ)) (D:=(484:ℝ)) (xi:=x5) (xj:=x6) (yi:=y5) (yj:=y6) (aj:=(2000:ℝ)) (bi:=(1000:ℝ)) (bj:=(2500:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx5U) (by exact hx6L) (by exact hsplit0) (by norm_num)
    linarith only [hh]
  have u20:y2≤(1716:ℝ):=by
    have hd:(x2-x5)^2≤(967:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u17
      · exact hx5L
      · exact u19
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1284:ℝ)) (D:=(967:ℝ)) (xi:=y2) (xj:=y5) (yi:=x2) (yj:=x5) (aj:=(2516:ℝ)) (bi:=(1742:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u4) (by exact u10) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u21:(1439:ℝ)≤x3:=by
    have hd:(y3-y2)^2≤(716:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact u18
      · exact u2
      · exact u20
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1439:ℝ)) (D:=(716:ℝ)) (xi:=x3) (xj:=x2) (yi:=y3) (yj:=y2) (ai:=(1426:ℝ)) (aj:=(0:ℝ)) (bj:=(148:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u5) (by exact u17) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have u22:y3≤(1793:ℝ):=by
    have hd:(x3-x6)^2≤(1061:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u21
      · exact u15
      · exact hx6L
      · exact hsplit0
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y3-y6)^2+(x3-x6)^2:=by nlinarith only [hT36]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1207:ℝ)) (D:=(1061:ℝ)) (xi:=y3) (xj:=y6) (yi:=x3) (yj:=x6) (aj:=(2516:ℝ)) (bi:=(1804:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u18) (by exact u11) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u23:(2865:ℝ)≤x4:=by
    have hd:(y4-y3)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u7
      · exact u9
      · exact hy3L
      · exact u22
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=x4) (xj:=x3) (yi:=y4) (yj:=y3) (ai:=(2852:ℝ)) (aj:=(1439:ℝ)) (bj:=(1574:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u16) (by exact u15) (by exact u21) (by norm_num)
    linarith only [hh]
  have u24:(2542:ℝ)≤y5:=by
    have hd:(x5-x2)^2≤(967:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact u19
      · exact hx2L
      · exact u17
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1284:ℝ)) (D:=(967:ℝ)) (xi:=y5) (xj:=y2) (yi:=x5) (yj:=x2) (ai:=(2516:ℝ)) (aj:=(1258:ℝ)) (bj:=(1716:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u10) (by exact u20) (by exact u2) (by norm_num)
    linarith only [hh]
  have u25:y0≤(458:ℝ):=by
    have hd:(x0-x2)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact hx0U
      · exact hx2L
      · exact u17
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y0) (xj:=y2) (yi:=x0) (yj:=x2) (aj:=(1258:ℝ)) (bi:=(484:ℝ)) (bj:=(1716:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u12) (by exact u2) (by exact u20) (by norm_num)
    linarith only [hh]
  have u26:x2≤(135:ℝ):=by
    have hd:(y2-y3)^2≤(716:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u2
      · exact u20
      · exact hy3L
      · exact u22
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1439:ℝ)) (D:=(716:ℝ)) (xi:=x2) (xj:=x3) (yi:=y2) (yj:=y3) (aj:=(1439:ℝ)) (bi:=(148:ℝ)) (bj:=(1574:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u17) (by exact u21) (by exact u15) (by norm_num)
    linarith only [hh]
  have u27:x0≤(967:ℝ):=by
    have hd:(y0-y1)^2≤(484:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hy0L
      · exact u25
      · exact hy1L
      · exact u13
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2:=by nlinarith only [hT01]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1533:ℝ)) (D:=(484:ℝ)) (xi:=x0) (xj:=x1) (yi:=y0) (yj:=y1) (aj:=(2000:ℝ)) (bi:=(1000:ℝ)) (bj:=(2500:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx0U) (by exact hx1L) (by exact hsplit1) (by norm_num)
    linarith only [hh]
  have u28:y0≤(432:ℝ):=by
    have hd:(x0-x2)^2≤(967:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact u27
      · exact hx2L
      · exact u26
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1284:ℝ)) (D:=(967:ℝ)) (xi:=y0) (xj:=y2) (yi:=x0) (yj:=x2) (aj:=(1258:ℝ)) (bi:=(458:ℝ)) (bj:=(1716:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u25) (by exact u2) (by exact u20) (by norm_num)
    linarith only [hh]
  have u29:(1284:ℝ)≤y2:=by
    have hd:(x2-x0)^2≤(967:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx2L
      · exact u26
      · exact hx0L
      · exact u27
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1284:ℝ)) (D:=(967:ℝ)) (xi:=y2) (xj:=y0) (yi:=x2) (yj:=x0) (ai:=(1258:ℝ)) (aj:=(0:ℝ)) (bj:=(432:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u2) (by exact u28) (by exact hy0L) (by norm_num)
    linarith only [hh]
  have u30:(1207:ℝ)≤y3:=by
    have hd:(x3-x1)^2≤(1061:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u21
      · exact u15
      · exact hx1L
      · exact hsplit1
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y3-y1)^2+(x3-x1)^2:=by nlinarith only [hT13]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1207:ℝ)) (D:=(1061:ℝ)) (xi:=y3) (xj:=y1) (yi:=x3) (yj:=x1) (ai:=(1000:ℝ)) (aj:=(0:ℝ)) (bj:=(484:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy3L) (by exact u13) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u31:(1524:ℝ)≤x3:=by
    have hd:(y3-y2)^2≤(509:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u30
      · exact u22
      · exact u29
      · exact u20
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1524:ℝ)) (D:=(509:ℝ)) (xi:=x3) (xj:=x2) (yi:=y3) (yj:=y2) (ai:=(1439:ℝ)) (aj:=(0:ℝ)) (bj:=(135:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u21) (by exact u26) (by exact hx2L) (by norm_num)
    linarith only [hh]
  have d0:(x3-x4)^2≤(1476:ℝ)^2:=by
    apply sqdiff_bound_contract
    · exact u31
    · exact u15
    · exact u23
    · exact hx4U
    · norm_num
    · norm_num
  have d2:(y3-y4)^2≤(535:ℝ)^2:=by
    apply sqdiff_bound_contract
    · exact u30
    · exact u22
    · exact u7
    · exact u9
    · norm_num
    · norm_num
  nlinarith only [hT34, d0, d2]
