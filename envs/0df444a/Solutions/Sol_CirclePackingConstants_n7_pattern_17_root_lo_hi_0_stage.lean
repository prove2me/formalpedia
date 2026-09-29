-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_17_root_lo_hi_0_stage
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:45:41.11973+00:00
-- url     : https://prove2.me/submissions/79727ffe-dab4-4af0-be26-7fffc2492380

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
noncomputable section
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

end N7Rep17Stages
end CirclePackingConstants

open CirclePackingConstants
open CirclePackingConstants.N7Rep17Stages

theorem solution (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(1000:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(458:ℝ))
 (hx1L:(2500:ℝ)≤x1 ) (hx1U:x1≤(3000:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(484:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(135:ℝ) ) (hy2L:(1258:ℝ)≤y2 ) (hy2U:y2≤(1716:ℝ))
 (hx3L:(1439:ℝ)≤x3 ) (hx3U:x3≤(1574:ℝ) ) (hy3L:(1000:ℝ)≤y3 ) (hy3U:y3≤(1793:ℝ))
 (hx4L:(2865:ℝ)≤x4 ) (hx4U:x4≤(3000:ℝ) ) (hy4L:(1258:ℝ)≤y4 ) (hy4U:y4≤(1742:ℝ))
 (hx5L:(0:ℝ)≤x5 ) (hx5U:x5≤(967:ℝ) ) (hy5L:(2542:ℝ)≤y5 ) (hy5U:y5≤(3000:ℝ))
 (hx6L:(2000:ℝ)≤x6 ) (hx6U:x6≤(2500:ℝ) ) (hy6L:(2516:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (0:ℝ)≤x0 ∧ x0≤(509:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(175:ℝ) ∧ (2550:ℝ)≤x1 ∧ x1≤(3000:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(199:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(89:ℝ) ∧ (1524:ℝ)≤y2 ∧ y2≤(1585:ℝ) ∧ (1497:ℝ)≤x3 ∧ x3≤(1574:ℝ) ∧ (1000:ℝ)≤y3 ∧ y3≤(1172:ℝ) ∧ (2923:ℝ)≤x4 ∧ x4≤(3000:ℝ) ∧ (1570:ℝ)≤y4 ∧ y4≤(1742:ℝ) ∧ (637:ℝ)≤x5 ∧ x5≤(763:ℝ) ∧ (2825:ℝ)≤y5 ∧ y5≤(3000:ℝ) ∧ (2000:ℝ)≤x6 ∧ x6≤(2332:ℝ) ∧ (2796:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: y1≤(215:ℝ):=by
  have hd:(x1-x4)^2≤(500:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx1L
   · exact hx1U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1527:ℝ) ) (D:=(500:ℝ) ) (xi:=y1 ) (xj:=y4 ) (yi:=x1 ) (yj:=x4 ) (aj:=(1258:ℝ) ) (bi:=(484:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy4L) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u1: (1527:ℝ)≤y4:=by
  have hd:(x4-x1)^2≤(500:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx4L
   · exact hx4U
   · exact hx1L
   · exact hx1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y1)^2+(x4-x1)^2:=by nlinarith only [hT14]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1527:ℝ) ) (D:=(500:ℝ) ) (xi:=y4 ) (xj:=y1 ) (yi:=x4 ) (yj:=x1 ) (ai:=(1258:ℝ) ) (aj:=(0:ℝ) ) (bj:=(215:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact u0) (by exact hy1L) (by norm_num)
  linarith only [hh]
 have u2: x6≤(2356:ℝ):=by
  have hd:(y6-y4)^2≤(1473:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy6L
   · exact hy6U
   · exact u1
   · exact hy4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x4)^2+(y6-y4)^2:=by nlinarith only [hT46]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(644:ℝ) ) (D:=(1473:ℝ) ) (xi:=x6 ) (xj:=x4 ) (yi:=y6 ) (yj:=y4 ) (aj:=(2865:ℝ) ) (bi:=(2500:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx6U) (by exact hx4L) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u3: (2785:ℝ)≤y6:=by
  have hd:(x6-x4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact u2
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y6 ) (xj:=y4 ) (yi:=x6 ) (yj:=x4 ) (ai:=(2516:ℝ) ) (aj:=(1527:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact hy4U) (by exact u1) (by norm_num)
  linarith only [hh]
 have u4: y3≤(1358:ℝ):=by
  have hd:(x3-x4)^2≤(1561:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx3L
   · exact hx3U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y4)^2+(x3-x4)^2:=by nlinarith only [hT34]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(384:ℝ) ) (D:=(1561:ℝ) ) (xi:=y3 ) (xj:=y4 ) (yi:=x3 ) (yj:=x4 ) (aj:=(1527:ℝ) ) (bi:=(1793:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3U) (by exact u1) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u5: x5≤(815:ℝ):=by
  have hd:(y5-y6)^2≤(458:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy5L
   · exact hy5U
   · exact u3
   · exact hy6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x6)^2+(y5-y6)^2:=by nlinarith only [hT56]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1541:ℝ) ) (D:=(458:ℝ) ) (xi:=x5 ) (xj:=x6 ) (yi:=y5 ) (yj:=y6 ) (aj:=(2000:ℝ) ) (bi:=(967:ℝ) ) (bj:=(2356:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5U) (by exact hx6L) (by exact u2) (by norm_num)
  linarith only [hh]
 have u6: x0≤(714:ℝ):=by
  have hd:(y0-y3)^2≤(1358:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact hy0U
   · exact hy3L
   · exact u4
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x3)^2+(y0-y3)^2:=by nlinarith only [hT03]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(860:ℝ) ) (D:=(1358:ℝ) ) (xi:=x0 ) (xj:=x3 ) (yi:=y0 ) (yj:=y3 ) (aj:=(1439:ℝ) ) (bi:=(1000:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0U) (by exact hx3L) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u7: (1440:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(714:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact hx2U
   · exact hx0L
   · exact u6
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1440:ℝ) ) (D:=(714:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1258:ℝ) ) (aj:=(0:ℝ) ) (bj:=(458:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2L) (by exact hy0U) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u8: y2≤(1615:ℝ):=by
  have hd:(x2-x5)^2≤(815:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact hx2U
   · exact hx5L
   · exact u5
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1385:ℝ) ) (D:=(815:ℝ) ) (xi:=y2 ) (xj:=y5 ) (yi:=x2 ) (yj:=x5 ) (aj:=(2542:ℝ) ) (bi:=(1716:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact hy5L) (by exact hy5U) (by norm_num)
  linarith only [hh]
 have u9: (1485:ℝ)≤x3:=by
  have hd:(y3-y2)^2≤(615:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact u4
   · exact u7
   · exact u8
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1485:ℝ) ) (D:=(615:ℝ) ) (xi:=x3 ) (xj:=x2 ) (yi:=y3 ) (yj:=y2 ) (ai:=(1439:ℝ) ) (aj:=(0:ℝ) ) (bj:=(135:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact hx2U) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u10: y3≤(1288:ℝ):=by
  have hd:(x3-x2)^2≤(1574:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u9
   · exact hx3U
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y2)^2+(x3-x2)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(327:ℝ) ) (D:=(1574:ℝ) ) (xi:=y3 ) (xj:=y2 ) (yi:=x3 ) (yj:=x2 ) (aj:=(1440:ℝ) ) (bi:=(1358:ℝ) ) (bj:=(1615:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u4) (by exact u7) (by exact u8) (by norm_num)
  linarith only [hh]
 have u11: y3≤(1204:ℝ):=by
  have hd:(x3-x4)^2≤(1515:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u9
   · exact hx3U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y4)^2+(x3-x4)^2:=by nlinarith only [hT34]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(538:ℝ) ) (D:=(1515:ℝ) ) (xi:=y3 ) (xj:=y4 ) (yi:=x3 ) (yj:=x4 ) (aj:=(1527:ℝ) ) (bi:=(1288:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u10) (by exact u1) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u12: (2911:ℝ)≤x4:=by
  have hd:(y4-y3)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u1
   · exact hy4U
   · exact hy3L
   · exact u11
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x4 ) (xj:=x3 ) (yi:=y4 ) (yj:=y3 ) (ai:=(2865:ℝ) ) (aj:=(1485:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx4L) (by exact hx3U) (by exact u9) (by norm_num)
  linarith only [hh]
 have u13: (1538:ℝ)≤y4:=by
  have hd:(x4-x3)^2≤(1515:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u12
   · exact hx4U
   · exact u9
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y3)^2+(x4-x3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(538:ℝ) ) (D:=(1515:ℝ) ) (xi:=y4 ) (xj:=y3 ) (yi:=x4 ) (yj:=x3 ) (ai:=(1527:ℝ) ) (aj:=(1000:ℝ) ) (bj:=(1204:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u11) (by exact hy3L) (by norm_num)
  linarith only [hh]
 have u14: (388:ℝ)≤x5:=by
  have hd:(y5-y2)^2≤(1560:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy5L
   · exact hy5U
   · exact u7
   · exact u8
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x2)^2+(y5-y2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(388:ℝ) ) (D:=(1560:ℝ) ) (xi:=x5 ) (xj:=x2 ) (yi:=y5 ) (yj:=y2 ) (ai:=(0:ℝ) ) (aj:=(0:ℝ) ) (bj:=(135:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5L) (by exact hx2U) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u15: (2825:ℝ)≤y5:=by
  have hd:(x5-x2)^2≤(815:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u14
   · exact u5
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1385:ℝ) ) (D:=(815:ℝ) ) (xi:=y5 ) (xj:=y2 ) (yi:=x5 ) (yj:=x2 ) (ai:=(2542:ℝ) ) (aj:=(1440:ℝ) ) (bj:=(1615:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy5L) (by exact u8) (by exact u7) (by norm_num)
  linarith only [hh]
 have u16: x5≤(763:ℝ):=by
  have hd:(y5-y6)^2≤(215:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u15
   · exact hy5U
   · exact u3
   · exact hy6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x6)^2+(y5-y6)^2:=by nlinarith only [hT56]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1593:ℝ) ) (D:=(215:ℝ) ) (xi:=x5 ) (xj:=x6 ) (yi:=y5 ) (yj:=y6 ) (aj:=(2000:ℝ) ) (bi:=(815:ℝ) ) (bj:=(2356:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u5) (by exact hx6L) (by exact u2) (by norm_num)
  linarith only [hh]
 have u17: x6≤(2332:ℝ):=by
  have hd:(y6-y4)^2≤(1462:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u3
   · exact hy6U
   · exact u13
   · exact hy4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x4)^2+(y6-y4)^2:=by nlinarith only [hT46]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(668:ℝ) ) (D:=(1462:ℝ) ) (xi:=x6 ) (xj:=x4 ) (yi:=y6 ) (yj:=y4 ) (aj:=(2911:ℝ) ) (bi:=(2356:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u2) (by exact u12) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u18: (2796:ℝ)≤y6:=by
  have hd:(x6-x4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact u17
   · exact u12
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y6 ) (xj:=y4 ) (yi:=x6 ) (yj:=x4 ) (ai:=(2785:ℝ) ) (aj:=(1538:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u3) (by exact hy4U) (by exact u13) (by norm_num)
  linarith only [hh]
 have u19: y0≤(175:ℝ):=by
  have hd:(x0-x2)^2≤(714:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx0L
   · exact u6
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1440:ℝ) ) (D:=(714:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1440:ℝ) ) (bi:=(458:ℝ) ) (bj:=(1615:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy0U) (by exact u7) (by exact u8) (by norm_num)
  linarith only [hh]
 have u20: x0≤(509:ℝ):=by
  have hd:(y0-y3)^2≤(1204:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact u19
   · exact hy3L
   · exact u11
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x3)^2+(y0-y3)^2:=by nlinarith only [hT03]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1065:ℝ) ) (D:=(1204:ℝ) ) (xi:=x0 ) (xj:=x3 ) (yi:=y0 ) (yj:=y3 ) (aj:=(1485:ℝ) ) (bi:=(714:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u6) (by exact u9) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u21: (2550:ℝ)≤x1:=by
  have hd:(y1-y3)^2≤(1204:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact u0
   · exact hy3L
   · exact u11
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x3)^2+(y1-y3)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1065:ℝ) ) (D:=(1204:ℝ) ) (xi:=x1 ) (xj:=x3 ) (yi:=y1 ) (yj:=y3 ) (ai:=(2500:ℝ) ) (aj:=(1485:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx1L) (by exact hx3U) (by exact u9) (by norm_num)
  linarith only [hh]
 have u22: y1≤(199:ℝ):=by
  have hd:(x1-x4)^2≤(450:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u21
   · exact hx1U
   · exact u12
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1543:ℝ) ) (D:=(450:ℝ) ) (xi:=y1 ) (xj:=y4 ) (yi:=x1 ) (yj:=x4 ) (aj:=(1538:ℝ) ) (bi:=(215:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact u13) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u23: (1524:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(509:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact hx2U
   · exact hx0L
   · exact u20
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1524:ℝ) ) (D:=(509:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1440:ℝ) ) (aj:=(0:ℝ) ) (bj:=(175:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u7) (by exact u19) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u24: x2≤(89:ℝ):=by
  have hd:(y2-y3)^2≤(615:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u23
   · exact u8
   · exact hy3L
   · exact u11
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1485:ℝ) ) (D:=(615:ℝ) ) (xi:=x2 ) (xj:=x3 ) (yi:=y2 ) (yj:=y3 ) (aj:=(1485:ℝ) ) (bi:=(135:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact u9) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u25: y2≤(1585:ℝ):=by
  have hd:(x2-x5)^2≤(763:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u24
   · exact u14
   · exact u16
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1415:ℝ) ) (D:=(763:ℝ) ) (xi:=y2 ) (xj:=y5 ) (yi:=x2 ) (yj:=x5 ) (aj:=(2825:ℝ) ) (bi:=(1615:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u8) (by exact u15) (by exact hy5U) (by norm_num)
  linarith only [hh]
 have u26: (1497:ℝ)≤x3:=by
  have hd:(y3-y2)^2≤(585:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact u11
   · exact u23
   · exact u25
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1497:ℝ) ) (D:=(585:ℝ) ) (xi:=x3 ) (xj:=x2 ) (yi:=y3 ) (yj:=y2 ) (ai:=(1485:ℝ) ) (aj:=(0:ℝ) ) (bj:=(89:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u9) (by exact u24) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u27: y3≤(1172:ℝ):=by
  have hd:(x3-x4)^2≤(1503:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u26
   · exact hx3U
   · exact u12
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y4)^2+(x3-x4)^2:=by nlinarith only [hT34]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(570:ℝ) ) (D:=(1503:ℝ) ) (xi:=y3 ) (xj:=y4 ) (yi:=x3 ) (yj:=x4 ) (aj:=(1538:ℝ) ) (bi:=(1204:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u11) (by exact u13) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u28: (1543:ℝ)≤y4:=by
  have hd:(x4-x1)^2≤(450:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u12
   · exact hx4U
   · exact u21
   · exact hx1U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y1)^2+(x4-x1)^2:=by nlinarith only [hT14]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1543:ℝ) ) (D:=(450:ℝ) ) (xi:=y4 ) (xj:=y1 ) (yi:=x4 ) (yj:=x1 ) (ai:=(1538:ℝ) ) (aj:=(0:ℝ) ) (bj:=(199:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u13) (by exact u22) (by exact hy1L) (by norm_num)
  linarith only [hh]
 have u29: (2923:ℝ)≤x4:=by
  have hd:(y4-y3)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u28
   · exact hy4U
   · exact hy3L
   · exact u27
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x4 ) (xj:=x3 ) (yi:=y4 ) (yj:=y3 ) (ai:=(2911:ℝ) ) (aj:=(1497:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u12) (by exact hx3U) (by exact u26) (by norm_num)
  linarith only [hh]
 have u30: (1570:ℝ)≤y4:=by
  have hd:(x4-x3)^2≤(1503:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u29
   · exact hx4U
   · exact u26
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y3)^2+(x4-x3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(570:ℝ) ) (D:=(1503:ℝ) ) (xi:=y4 ) (xj:=y3 ) (yi:=x4 ) (yj:=x3 ) (ai:=(1543:ℝ) ) (aj:=(1000:ℝ) ) (bj:=(1172:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u28) (by exact u27) (by exact hy3L) (by norm_num)
  linarith only [hh]
 have u31: (637:ℝ)≤x5:=by
  have hd:(y5-y2)^2≤(1476:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u15
   · exact hy5U
   · exact u23
   · exact u25
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x2)^2+(y5-y2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(637:ℝ) ) (D:=(1476:ℝ) ) (xi:=x5 ) (xj:=x2 ) (yi:=y5 ) (yj:=y2 ) (ai:=(388:ℝ) ) (aj:=(0:ℝ) ) (bj:=(89:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u14) (by exact u24) (by exact hx2L) (by norm_num)
  linarith only [hh]
 exact ⟨hx0L,u20,hy0L,u19,u21,hx1U,hy1L,u22,hx2L,u24,u23,u25,u26,hx3U,hy3L,u27,u29,hx4U,u30,hy4U,u31,u16,u15,hy5U,hx6L,u17,u18,hy6U⟩
