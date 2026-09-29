-- Prove2me | solution 1 for CirclePackingConstants.N7Rep02.n7_pattern_02_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T00:12:30.847989+00:00
-- url     : https://prove2.me/submissions/fda902d0-5f63-4ad7-b9d6-236f173975f4

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
noncomputable section
namespace CirclePackingConstants
namespace N7Rep02


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
end N7Rep02
end CirclePackingConstants

open CirclePackingConstants
open CirclePackingConstants.N7Rep02

theorem solution (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L:(1000:ℝ)≤x0) (hx0U:x0≤(2000:ℝ)) (hy0L:(0:ℝ)≤y0) (hy0U:y0≤(1000:ℝ))
  (hx1L:(0:ℝ)≤x1) (hx1U:x1≤(1000:ℝ)) (hy1L:(1000:ℝ)≤y1) (hy1U:y1≤(2000:ℝ))
  (hx2L:(1000:ℝ)≤x2) (hx2U:x2≤(2000:ℝ)) (hy2L:(1000:ℝ)≤y2) (hy2U:y2≤(2000:ℝ))
  (hx3L:(2000:ℝ)≤x3) (hx3U:x3≤(3000:ℝ)) (hy3L:(1000:ℝ)≤y3) (hy3U:y3≤(2000:ℝ))
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
  have u1:x1≤(742:ℝ):=by
    have hd:(y1-y2)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact hy1U
      · exact hy2L
      · exact hy2U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x1-x2)^2+(y1-y2)^2:=by nlinarith only [hT12]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=x1) (xj:=x2) (yi:=y1) (yj:=y2) (aj:=(1000:ℝ)) (bi:=(1000:ℝ)) (bj:=(2000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx1U) (by exact hx2L) (by exact hx2U) (by norm_num)
    linarith only [hh]
  have u2:y1≤(1742:ℝ):=by
    have hd:(x1-x4)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact u1
      · exact hx4L
      · exact hx4U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y1) (xj:=y4) (yi:=x1) (yj:=x4) (aj:=(2000:ℝ)) (bi:=(2000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy4L) (by exact hy4U) (by norm_num)
    linarith only [hh]
  have u3:(1258:ℝ)≤y2:=by
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
  have u4:(1258:ℝ)≤x2:=by
    have hd:(y2-y1)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u3
      · exact hy2U
      · exact hy1L
      · exact u2
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x2-x1)^2+(y2-y1)^2:=by nlinarith only [hT12]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=x2) (xj:=x1) (yi:=y2) (yj:=y1) (ai:=(1000:ℝ)) (aj:=(0:ℝ)) (bj:=(742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx2L) (by exact u1) (by exact hx1L) (by norm_num)
    linarith only [hh]
  have u5:x2≤(1742:ℝ):=by
    have hd:(y2-y3)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u3
      · exact hy2U
      · exact hy3L
      · exact hy3U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=x2) (xj:=x3) (yi:=y2) (yj:=y3) (aj:=(2000:ℝ)) (bi:=(2000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
    linarith only [hh]
  have u6:y2≤(1574:ℝ):=by
    have hd:(x2-x5)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u4
      · exact u5
      · exact hx5L
      · exact hx5U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=y2) (xj:=y5) (yi:=x2) (yj:=x5) (aj:=(2000:ℝ)) (bi:=(2000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact hy5L) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u7:(2684:ℝ)≤x3:=by
    have hd:(y3-y2)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hy3L
      · exact hy3U
      · exact u3
      · exact u6
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=x3) (xj:=x2) (yi:=y3) (yj:=y2) (ai:=(2000:ℝ)) (aj:=(1258:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact u5) (by exact u4) (by norm_num)
    linarith only [hh]
  have u8:y3≤(1742:ℝ):=by
    have hd:(x3-x6)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u7
      · exact hx3U
      · exact hx6L
      · exact hx6U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y3-y6)^2+(x3-x6)^2:=by nlinarith only [hT36]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y3) (xj:=y6) (yi:=x3) (yj:=x6) (aj:=(2000:ℝ)) (bi:=(2000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy3U) (by exact hy6L) (by exact hy6U) (by norm_num)
    linarith only [hh]
  have u9:(2258:ℝ)≤y4:=by
    have hd:(x4-x1)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx4L
      · exact hx4U
      · exact hx1L
      · exact u1
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y4-y1)^2+(x4-x1)^2:=by nlinarith only [hT14]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y4) (xj:=y1) (yi:=x4) (yj:=x1) (ai:=(2000:ℝ)) (aj:=(1000:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact u2) (by exact hy1L) (by norm_num)
    linarith only [hh]
  have u10:x4≤(742:ℝ):=by
    have hd:(y4-y5)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u9
      · exact hy4U
      · exact hy5L
      · exact hy5U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x4-x5)^2+(y4-y5)^2:=by nlinarith only [hT45]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=x4) (xj:=x5) (yi:=y4) (yj:=y5) (aj:=(1000:ℝ)) (bi:=(1000:ℝ)) (bj:=(2000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx4U) (by exact hx5L) (by exact hx5U) (by norm_num)
    linarith only [hh]
  have u11:(2684:ℝ)≤y5:=by
    have hd:(x5-x2)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx5L
      · exact hx5U
      · exact u4
      · exact u5
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=y5) (xj:=y2) (yi:=x5) (yj:=x2) (ai:=(2000:ℝ)) (aj:=(1258:ℝ)) (bj:=(1574:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy5L) (by exact u6) (by exact u3) (by norm_num)
    linarith only [hh]
  have u12:(1426:ℝ)≤x5:=by
    have hd:(y5-y4)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u11
      · exact hy5U
      · exact u9
      · exact hy4U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x5-x4)^2+(y5-y4)^2:=by nlinarith only [hT45]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=x5) (xj:=x4) (yi:=y5) (yj:=y4) (ai:=(1000:ℝ)) (aj:=(0:ℝ)) (bj:=(742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx5L) (by exact u10) (by exact hx4L) (by norm_num)
    linarith only [hh]
  have u13:x5≤(1742:ℝ):=by
    have hd:(y5-y6)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u11
      · exact hy5U
      · exact hy6L
      · exact hy6U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x5-x6)^2+(y5-y6)^2:=by nlinarith only [hT56]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=x5) (xj:=x6) (yi:=y5) (yj:=y6) (aj:=(2000:ℝ)) (bi:=(2000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
    linarith only [hh]
  have u14:(2258:ℝ)≤y6:=by
    have hd:(x6-x3)^2≤(1000:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx6L
      · exact hx6U
      · exact u7
      · exact hx3U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y6-y3)^2+(x6-x3)^2:=by nlinarith only [hT36]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1258:ℝ)) (D:=(1000:ℝ)) (xi:=y6) (xj:=y3) (yi:=x6) (yj:=x3) (ai:=(2000:ℝ)) (aj:=(1000:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact u8) (by exact hy3L) (by norm_num)
    linarith only [hh]
  have u15:(2852:ℝ)≤x6:=by
    have hd:(y6-y5)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u14
      · exact hy6U
      · exact u11
      · exact hy5U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x6-x5)^2+(y6-y5)^2:=by nlinarith only [hT56]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=x6) (xj:=x5) (yi:=y6) (yj:=y5) (ai:=(2000:ℝ)) (aj:=(1426:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hx6L) (by exact u13) (by exact u12) (by norm_num)
    linarith only [hh]
  have u16:y6≤(2673:ℝ):=by
    have hd:(x6-x5)^2≤(1574:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u15
      · exact hx6U
      · exact u12
      · exact u13
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y6-y5)^2+(x6-x5)^2:=by nlinarith only [hT56]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(327:ℝ)) (D:=(1574:ℝ)) (xi:=y6) (xj:=y5) (yi:=x6) (yj:=x5) (aj:=(2684:ℝ)) (bi:=(3000:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact hy6U) (by exact u11) (by exact hy5U) (by norm_num)
    linarith only [hh]
  have u17:y0≤(148:ℝ):=by
    have hd:(x0-x2)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx0L
      · exact hx0U
      · exact u4
      · exact u5
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=y0) (xj:=y2) (yi:=x0) (yj:=x2) (aj:=(1258:ℝ)) (bi:=(742:ℝ)) (bj:=(1574:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact u3) (by exact u6) (by norm_num)
    linarith only [hh]
  have u18:x1≤(241:ℝ):=by
    have hd:(y1-y2)^2≤(574:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hy1L
      · exact u2
      · exact u3
      · exact u6
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x1-x2)^2+(y1-y2)^2:=by nlinarith only [hT12]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1501:ℝ)) (D:=(574:ℝ)) (xi:=x1) (xj:=x2) (yi:=y1) (yj:=y2) (aj:=(1258:ℝ)) (bi:=(742:ℝ)) (bj:=(1742:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u4) (by exact u5) (by norm_num)
    linarith only [hh]
  have u19:y1≤(1574:ℝ):=by
    have hd:(x1-x4)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact hx1L
      · exact u18
      · exact hx4L
      · exact u10
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
    have hh:=force_upper_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=y1) (xj:=y4) (yi:=x1) (yj:=x4) (aj:=(2258:ℝ)) (bi:=(1742:ℝ)) (bj:=(3000:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u2) (by exact u9) (by exact hy4U) (by norm_num)
    linarith only [hh]
  have u20:(1426:ℝ)≤y2:=by
    have hd:(x2-x0)^2≤(742:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u4
      · exact u5
      · exact hx0L
      · exact hx0U
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1426:ℝ)) (D:=(742:ℝ)) (xi:=y2) (xj:=y0) (yi:=x2) (yj:=x0) (ai:=(1258:ℝ)) (aj:=(0:ℝ)) (bj:=(148:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u3) (by exact u17) (by exact hy0L) (by norm_num)
    linarith only [hh]
  have u21:(1501:ℝ)≤x2:=by
    have hd:(y2-y1)^2≤(574:ℝ)^2:=by
      apply sqdiff_bound_contract
      · exact u20
      · exact u6
      · exact hy1L
      · exact u19
      · norm_num
      · norm_num
    have hs:(2584683:ℝ)<(x2-x1)^2+(y2-y1)^2:=by nlinarith only [hT12]
    have hh:=force_lower_contract (T:=(2584683:ℝ)) (q:=(1501:ℝ)) (D:=(574:ℝ)) (xi:=x2) (xj:=x1) (yi:=y2) (yj:=y1) (ai:=(1258:ℝ)) (aj:=(0:ℝ)) (bj:=(241:ℝ)) (by norm_num) hs hd (by norm_num) (by exact u4) (by exact u18) (by exact hx1L) (by norm_num)
    linarith only [hh]
  have d0:(x2-x3)^2≤(1499:ℝ)^2:=by
    apply sqdiff_bound_contract
    · exact u21
    · exact u5
    · exact u7
    · exact hx3U
    · norm_num
    · norm_num
  have d2:(y2-y3)^2≤(574:ℝ)^2:=by
    apply sqdiff_bound_contract
    · exact u20
    · exact u6
    · exact hy3L
    · exact u8
    · norm_num
    · norm_num
  nlinarith only [hT23, d0, d2]
