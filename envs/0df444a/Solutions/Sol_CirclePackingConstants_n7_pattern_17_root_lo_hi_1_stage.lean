-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_17_root_lo_hi_1_stage
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:47:14.288322+00:00
-- url     : https://prove2.me/submissions/73002caa-c98f-4123-97e2-ac15624cd636

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
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(509:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(175:ℝ))
 (hx1L:(2550:ℝ)≤x1 ) (hx1U:x1≤(3000:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(199:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(89:ℝ) ) (hy2L:(1524:ℝ)≤y2 ) (hy2U:y2≤(1585:ℝ))
 (hx3L:(1497:ℝ)≤x3 ) (hx3U:x3≤(1574:ℝ) ) (hy3L:(1000:ℝ)≤y3 ) (hy3U:y3≤(1172:ℝ))
 (hx4L:(2923:ℝ)≤x4 ) (hx4U:x4≤(3000:ℝ) ) (hy4L:(1570:ℝ)≤y4 ) (hy4U:y4≤(1742:ℝ))
 (hx5L:(637:ℝ)≤x5 ) (hx5U:x5≤(763:ℝ) ) (hy5L:(2825:ℝ)≤y5 ) (hy5U:y5≤(3000:ℝ))
 (hx6L:(2000:ℝ)≤x6 ) (hx6U:x6≤(2332:ℝ) ) (hy6L:(2796:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
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
 : (269:ℝ)≤x0 ∧ x0≤(474:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(61:ℝ) ∧ (2597:ℝ)≤x1 ∧ x1≤(3000:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(186:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(74:ℝ) ∧ (1536:ℝ)≤y2 ∧ y2≤(1572:ℝ) ∧ (1502:ℝ)≤x3 ∧ x3≤(1574:ℝ) ∧ (1000:ℝ)≤y3 ∧ y3≤(1159:ℝ) ∧ (2994:ℝ)≤x4 ∧ x4≤(3000:ℝ) ∧ (1583:ℝ)≤y4 ∧ y4≤(1586:ℝ) ∧ (664:ℝ)≤x5 ∧ x5≤(668:ℝ) ∧ (2964:ℝ)≤y5 ∧ y5≤(3000:ℝ) ∧ (2235:ℝ)≤x6 ∧ x6≤(2241:ℝ) ∧ (2997:ℝ)≤y6 ∧ y6≤(3000:ℝ) := by
 have u0: (2939:ℝ)≤y5:=by
  have hd:(x5-x2)^2≤(763:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx5L
   · exact hx5U
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1415:ℝ) ) (D:=(763:ℝ) ) (xi:=y5 ) (xj:=y2 ) (yi:=x5 ) (yj:=x2 ) (ai:=(2825:ℝ) ) (aj:=(1524:ℝ) ) (bj:=(1585:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy5L) (by exact hy2U) (by exact hy2L) (by norm_num)
  linarith only [hh]
 have u1: x5≤(738:ℝ):=by
  have hd:(y5-y6)^2≤(204:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u0
   · exact hy5U
   · exact hy6L
   · exact hy6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x6)^2+(y5-y6)^2:=by nlinarith only [hT56]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1594:ℝ) ) (D:=(204:ℝ) ) (xi:=x5 ) (xj:=x6 ) (yi:=y5 ) (yj:=y6 ) (aj:=(2000:ℝ) ) (bi:=(763:ℝ) ) (bj:=(2332:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5U) (by exact hx6L) (by exact hx6U) (by norm_num)
  linarith only [hh]
 have u2: x6≤(2266:ℝ):=by
  have hd:(y6-y4)^2≤(1430:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy6L
   · exact hy6U
   · exact hy4L
   · exact hy4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x4)^2+(y6-y4)^2:=by nlinarith only [hT46]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(734:ℝ) ) (D:=(1430:ℝ) ) (xi:=x6 ) (xj:=x4 ) (yi:=y6 ) (yj:=y4 ) (aj:=(2923:ℝ) ) (bi:=(2332:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx6U) (by exact hx4L) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u3: (2828:ℝ)≤y6:=by
  have hd:(x6-x4)^2≤(1000:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx6L
   · exact u2
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1258:ℝ) ) (D:=(1000:ℝ) ) (xi:=y6 ) (xj:=y4 ) (yi:=x6 ) (yj:=x4 ) (ai:=(2796:ℝ) ) (aj:=(1570:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy6L) (by exact hy4U) (by exact hy4L) (by norm_num)
  linarith only [hh]
 have u4: (2235:ℝ)≤x6:=by
  have hd:(y6-y5)^2≤(172:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u3
   · exact hy6U
   · exact u0
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x5)^2+(y6-y5)^2:=by nlinarith only [hT56]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1598:ℝ) ) (D:=(172:ℝ) ) (xi:=x6 ) (xj:=x5 ) (yi:=y6 ) (yj:=y5 ) (ai:=(2000:ℝ) ) (aj:=(637:ℝ) ) (bj:=(738:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx6L) (by exact u1) (by exact hx5L) (by norm_num)
  linarith only [hh]
 have u5: (269:ℝ)≤x0:=by
  have hd:(y0-y2)^2≤(1585:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact hy0U
   · exact hy2L
   · exact hy2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x2)^2+(y0-y2)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(269:ℝ) ) (D:=(1585:ℝ) ) (xi:=x0 ) (xj:=x2 ) (yi:=y0 ) (yj:=y2 ) (ai:=(0:ℝ) ) (aj:=(0:ℝ) ) (bj:=(89:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0L) (by exact hx2U) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u6: y0≤(61:ℝ):=by
  have hd:(x0-x2)^2≤(509:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u5
   · exact hx0U
   · exact hx2L
   · exact hx2U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y0-y2)^2+(x0-x2)^2:=by nlinarith only [hT02]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1524:ℝ) ) (D:=(509:ℝ) ) (xi:=y0 ) (xj:=y2 ) (yi:=x0 ) (yj:=x2 ) (aj:=(1524:ℝ) ) (bi:=(175:ℝ) ) (bj:=(1585:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy0U) (by exact hy2L) (by exact hy2U) (by norm_num)
  linarith only [hh]
 have u7: x0≤(474:ℝ):=by
  have hd:(y0-y3)^2≤(1172:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy0L
   · exact u6
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x0-x3)^2+(y0-y3)^2:=by nlinarith only [hT03]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1100:ℝ) ) (D:=(1172:ℝ) ) (xi:=x0 ) (xj:=x3 ) (yi:=y0 ) (yj:=y3 ) (aj:=(1497:ℝ) ) (bi:=(509:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx0U) (by exact hx3L) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u8: (2597:ℝ)≤x1:=by
  have hd:(y1-y3)^2≤(1172:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy1L
   · exact hy1U
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x1-x3)^2+(y1-y3)^2:=by nlinarith only [hT13]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1100:ℝ) ) (D:=(1172:ℝ) ) (xi:=x1 ) (xj:=x3 ) (yi:=y1 ) (yj:=y3 ) (ai:=(2550:ℝ) ) (aj:=(1497:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx1L) (by exact hx3U) (by exact hx3L) (by norm_num)
  linarith only [hh]
 have u9: y1≤(186:ℝ):=by
  have hd:(x1-x4)^2≤(403:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u8
   · exact hx1U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y1-y4)^2+(x1-x4)^2:=by nlinarith only [hT14]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1556:ℝ) ) (D:=(403:ℝ) ) (xi:=y1 ) (xj:=y4 ) (yi:=x1 ) (yj:=x4 ) (aj:=(1570:ℝ) ) (bi:=(199:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy1U) (by exact hy4L) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u10: (1536:ℝ)≤y2:=by
  have hd:(x2-x0)^2≤(474:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact hx2U
   · exact u5
   · exact u7
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y0)^2+(x2-x0)^2:=by nlinarith only [hT02]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1536:ℝ) ) (D:=(474:ℝ) ) (xi:=y2 ) (xj:=y0 ) (yi:=x2 ) (yj:=x0 ) (ai:=(1524:ℝ) ) (aj:=(0:ℝ) ) (bj:=(61:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2L) (by exact u6) (by exact hy0L) (by norm_num)
  linarith only [hh]
 have u11: x2≤(77:ℝ):=by
  have hd:(y2-y3)^2≤(585:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u10
   · exact hy2U
   · exact hy3L
   · exact hy3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2:=by nlinarith only [hT23]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1497:ℝ) ) (D:=(585:ℝ) ) (xi:=x2 ) (xj:=x3 ) (yi:=y2 ) (yj:=y3 ) (aj:=(1497:ℝ) ) (bi:=(89:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx2U) (by exact hx3L) (by exact hx3U) (by norm_num)
  linarith only [hh]
 have u12: x2≤(74:ℝ):=by
  have hd:(y2-y5)^2≤(1464:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u10
   · exact hy2U
   · exact u0
   · exact hy5U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x2-x5)^2+(y2-y5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(664:ℝ) ) (D:=(1464:ℝ) ) (xi:=x2 ) (xj:=x5 ) (yi:=y2 ) (yj:=y5 ) (aj:=(637:ℝ) ) (bi:=(77:ℝ) ) (bj:=(738:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u11) (by exact hx5L) (by exact u1) (by norm_num)
  linarith only [hh]
 have u13: y2≤(1572:ℝ):=by
  have hd:(x2-x5)^2≤(738:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hx2L
   · exact u12
   · exact hx5L
   · exact u1
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y2-y5)^2+(x2-x5)^2:=by nlinarith only [hT25]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1428:ℝ) ) (D:=(738:ℝ) ) (xi:=y2 ) (xj:=y5 ) (yi:=x2 ) (yj:=x5 ) (aj:=(2939:ℝ) ) (bi:=(1585:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy2U) (by exact u0) (by exact hy5U) (by norm_num)
  linarith only [hh]
 have u14: (1502:ℝ)≤x3:=by
  have hd:(y3-y2)^2≤(572:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy3L
   · exact hy3U
   · exact u10
   · exact u13
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x3-x2)^2+(y3-y2)^2:=by nlinarith only [hT23]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1502:ℝ) ) (D:=(572:ℝ) ) (xi:=x3 ) (xj:=x2 ) (yi:=y3 ) (yj:=y2 ) (ai:=(1497:ℝ) ) (aj:=(0:ℝ) ) (bj:=(74:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx3L) (by exact u12) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u15: y3≤(1159:ℝ):=by
  have hd:(x3-x4)^2≤(1498:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u14
   · exact hx3U
   · exact hx4L
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y3-y4)^2+(x3-x4)^2:=by nlinarith only [hT34]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(583:ℝ) ) (D:=(1498:ℝ) ) (xi:=y3 ) (xj:=y4 ) (yi:=x3 ) (yj:=x4 ) (aj:=(1570:ℝ) ) (bi:=(1172:ℝ) ) (bj:=(1742:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy3U) (by exact hy4L) (by exact hy4U) (by norm_num)
  linarith only [hh]
 have u16: (2928:ℝ)≤x4:=by
  have hd:(y4-y3)^2≤(742:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact hy4L
   · exact hy4U
   · exact hy3L
   · exact u15
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x3)^2+(y4-y3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1426:ℝ) ) (D:=(742:ℝ) ) (xi:=x4 ) (xj:=x3 ) (yi:=y4 ) (yj:=y3 ) (ai:=(2923:ℝ) ) (aj:=(1502:ℝ) ) (bj:=(1574:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx4L) (by exact hx3U) (by exact u14) (by norm_num)
  linarith only [hh]
 have u17: (1583:ℝ)≤y4:=by
  have hd:(x4-x3)^2≤(1498:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u16
   · exact hx4U
   · exact u14
   · exact hx3U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y3)^2+(x4-x3)^2:=by nlinarith only [hT34]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(583:ℝ) ) (D:=(1498:ℝ) ) (xi:=y4 ) (xj:=y3 ) (yi:=x4 ) (yj:=x3 ) (ai:=(1570:ℝ) ) (aj:=(1000:ℝ) ) (bj:=(1159:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4L) (by exact u15) (by exact hy3L) (by norm_num)
  linarith only [hh]
 have u18: (2994:ℝ)≤x4:=by
  have hd:(y4-y6)^2≤(1417:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u17
   · exact hy4U
   · exact u3
   · exact hy6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x4-x6)^2+(y4-y6)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(759:ℝ) ) (D:=(1417:ℝ) ) (xi:=x4 ) (xj:=x6 ) (yi:=y4 ) (yj:=y6 ) (ai:=(2928:ℝ) ) (aj:=(2235:ℝ) ) (bj:=(2266:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u16) (by exact u2) (by exact u4) (by norm_num)
  linarith only [hh]
 have u19: y4≤(1586:ℝ):=by
  have hd:(x4-x6)^2≤(765:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u18
   · exact hx4U
   · exact u4
   · exact u2
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y4-y6)^2+(x4-x6)^2:=by nlinarith only [hT46]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1414:ℝ) ) (D:=(765:ℝ) ) (xi:=y4 ) (xj:=y6 ) (yi:=x4 ) (yj:=x6 ) (aj:=(2828:ℝ) ) (bi:=(1742:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hy4U) (by exact u3) (by exact hy6U) (by norm_num)
  linarith only [hh]
 have u20: (664:ℝ)≤x5:=by
  have hd:(y5-y2)^2≤(1464:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u0
   · exact hy5U
   · exact u10
   · exact u13
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x2)^2+(y5-y2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(664:ℝ) ) (D:=(1464:ℝ) ) (xi:=x5 ) (xj:=x2 ) (yi:=y5 ) (yj:=y2 ) (ai:=(637:ℝ) ) (aj:=(0:ℝ) ) (bj:=(74:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact hx5L) (by exact u12) (by exact hx2L) (by norm_num)
  linarith only [hh]
 have u21: (2964:ℝ)≤y5:=by
  have hd:(x5-x2)^2≤(738:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u20
   · exact u1
   · exact hx2L
   · exact u12
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y5-y2)^2+(x5-x2)^2:=by nlinarith only [hT25]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1428:ℝ) ) (D:=(738:ℝ) ) (xi:=y5 ) (xj:=y2 ) (yi:=x5 ) (yj:=x2 ) (ai:=(2939:ℝ) ) (aj:=(1536:ℝ) ) (bj:=(1572:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u0) (by exact u13) (by exact u10) (by norm_num)
  linarith only [hh]
 have u22: x5≤(668:ℝ):=by
  have hd:(y5-y6)^2≤(172:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u21
   · exact hy5U
   · exact u3
   · exact hy6U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x5-x6)^2+(y5-y6)^2:=by nlinarith only [hT56]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(1598:ℝ) ) (D:=(172:ℝ) ) (xi:=x5 ) (xj:=x6 ) (yi:=y5 ) (yj:=y6 ) (aj:=(2235:ℝ) ) (bi:=(738:ℝ) ) (bj:=(2266:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u1) (by exact u4) (by exact u2) (by norm_num)
  linarith only [hh]
 have u23: x6≤(2241:ℝ):=by
  have hd:(y6-y4)^2≤(1417:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u3
   · exact hy6U
   · exact u17
   · exact u19
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(x6-x4)^2+(y6-y4)^2:=by nlinarith only [hT46]
  have hh:=force_upper_contract (T:=(2584683:ℝ) ) (q:=(759:ℝ) ) (D:=(1417:ℝ) ) (xi:=x6 ) (xj:=x4 ) (yi:=y6 ) (yj:=y4 ) (aj:=(2994:ℝ) ) (bi:=(2266:ℝ) ) (bj:=(3000:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u2) (by exact u18) (by exact hx4U) (by norm_num)
  linarith only [hh]
 have u24: (2997:ℝ)≤y6:=by
  have hd:(x6-x4)^2≤(765:ℝ)^2:=by
   apply sqdiff_bound_contract
   · exact u4
   · exact u23
   · exact u18
   · exact hx4U
   · norm_num
   · norm_num
  have hs:(2584683:ℝ)<(y6-y4)^2+(x6-x4)^2:=by nlinarith only [hT46]
  have hh:=force_lower_contract (T:=(2584683:ℝ) ) (q:=(1414:ℝ) ) (D:=(765:ℝ) ) (xi:=y6 ) (xj:=y4 ) (yi:=x6 ) (yj:=x4 ) (ai:=(2828:ℝ) ) (aj:=(1583:ℝ) ) (bj:=(1586:ℝ) ) (by norm_num) hs hd (by norm_num) (by exact u3) (by exact u19) (by exact u17) (by norm_num)
  linarith only [hh]
 exact ⟨u5,u7,hy0L,u6,u8,hx1U,hy1L,u9,hx2L,u12,u10,u13,u14,hx3U,hy3L,u15,u18,hx4U,u17,u19,u20,u22,u21,hy5U,u4,u23,u24,hy6U⟩
