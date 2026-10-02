-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_17_root_hi_0_stage
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:04:33.548686+00:00
-- url     : https://prove2.me/submissions/6c76cfcd-a782-4dc1-9250-3318428b02e5

import Mathlib

set_option autoImplicit false

theorem cut7 (u v D ul uh vl vh Mu Mv : ℝ) (h : D < u^2+v^2) (h1 : ul ≤ u) (h2 : u ≤ uh)
    (h3 : vl ≤ v) (h4 : v ≤ vh) (e1 : ul^2 ≤ Mu) (e2 : uh^2 ≤ Mu) (e3 : vl^2 ≤ Mv) (e4 : vh^2 ≤ Mv)
    (e5 : Mu + Mv ≤ D) : False := by
  have hu : u^2 ≤ Mu := by
    rcases le_total 0 u with h | h <;> nlinarith
  have hv : v^2 ≤ Mv := by
    rcases le_total 0 v with h | h <;> nlinarith
  linarith

set_option maxHeartbeats 1000000 in
theorem solution (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
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
  have s0 : y4 ≤ (1473:ℝ) := le_of_not_gt fun hc =>
    cut7 (x4-x6) (y4-y6) 2584683 (-148:ℝ) (500:ℝ) (-1527:ℝ) (-774:ℝ) (250000:ℝ) (2331729:ℝ) hT46 (by linarith only [hx4L, hx6U]) (by linarith only [hx4U, hx6L]) (by linarith only [hc, hy6U]) (by linarith only [hy4U, hy6L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2 : x1 ≤ (2356:ℝ) := le_of_not_gt fun hc =>
    cut7 (x1-x4) (y1-y4) 2584683 (-644:ℝ) (148:ℝ) (-1473:ℝ) (-774:ℝ) (414736:ℝ) (2169729:ℝ) hT14 (by linarith only [hc, hx4U]) (by linarith only [hx1U, hx4L]) (by linarith only [hy1L, s0]) (by linarith only [hy1U, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s3 : y1 ≤ (215:ℝ) := le_of_not_gt fun hc =>
    cut7 (x1-x4) (y1-y4) 2584683 (-1000:ℝ) (-496:ℝ) (-1258:ℝ) (-774:ℝ) (1000000:ℝ) (1582564:ℝ) hT14 (by linarith only [hx1L, hx4U]) (by linarith only [s2, hx4L]) (by linarith only [hc, s0]) (by linarith only [hy1U, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4 : (1311:ℝ) ≤ y3 := le_of_not_gt fun hc =>
    cut7 (x1-x3) (y1-y3) 2584683 (426:ℝ) (930:ℝ) (-1311:ℝ) (-785:ℝ) (864900:ℝ) (1718721:ℝ) hT13 (by linarith only [hx1L, hx3U]) (by linarith only [s2, hx3L]) (by linarith only [hy1L, hc]) (by linarith only [s3, hy3L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s5 : (1585:ℝ) ≤ y3 := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1574:ℝ) (-1278:ℝ) (-162:ℝ) (327:ℝ) (2477476:ℝ) (106929:ℝ) hT34 (by linarith only [hx3L, hx4U]) (by linarith only [hx3U, hx4L]) (by linarith only [s4, s0]) (by linarith only [hc, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s6 : x5 ≤ (811:ℝ) := le_of_not_gt fun hc =>
    cut7 (x3-x5) (y3-y5) 2584683 (426:ℝ) (763:ℝ) (-1415:ℝ) (-516:ℝ) (582169:ℝ) (2002225:ℝ) hT35 (by linarith only [hx3L, hx5U]) (by linarith only [hx3U, hc]) (by linarith only [s5, hy5U]) (by linarith only [hy3U, hy5L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s7 : x0 ≤ (823:ℝ) := le_of_not_gt fun hc =>
    cut7 (x0-x1) (y0-y1) 2584683 (-1533:ℝ) (-1000:ℝ) (-215:ℝ) (484:ℝ) (2350089:ℝ) (234256:ℝ) hT01 (by linarith only [hc, s2]) (by linarith only [hx0U, hx1L]) (by linarith only [hy0L, s3]) (by linarith only [hy0U, hy1L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8 : y0 ≤ (361:ℝ) := le_of_not_gt fun hc =>
    cut7 (x0-x2) (y0-y2) 2584683 (-148:ℝ) (823:ℝ) (-1381:ℝ) (-774:ℝ) (677329:ℝ) (1907161:ℝ) hT02 (by linarith only [hx0L, hx2U]) (by linarith only [s7, hx2L]) (by linarith only [hc, hy2U]) (by linarith only [hy0U, hy2L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s9 : (1381:ℝ) ≤ y2 := le_of_not_gt fun hc =>
    cut7 (x0-x2) (y0-y2) 2584683 (-148:ℝ) (823:ℝ) (-1381:ℝ) (-897:ℝ) (677329:ℝ) (1907161:ℝ) hT02 (by linarith only [hx0L, hx2U]) (by linarith only [s7, hx2L]) (by linarith only [hy0L, hc]) (by linarith only [s8, hy2L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s10 : x2 ≤ (91:ℝ) := le_of_not_gt fun hc =>
    cut7 (x2-x3) (y2-y3) 2584683 (-1483:ℝ) (-1278:ℝ) (-619:ℝ) (157:ℝ) (2199289:ℝ) (383161:ℝ) hT23 (by linarith only [hc, hx3U]) (by linarith only [hx2U, hx3L]) (by linarith only [s9, hy3U]) (by linarith only [hy2U, s5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s11 : y2 ≤ (1673:ℝ) := le_of_not_gt fun hc =>
    cut7 (x2-x3) (y2-y3) 2584683 (-1574:ℝ) (-1335:ℝ) (-327:ℝ) (157:ℝ) (2477476:ℝ) (106929:ℝ) hT23 (by linarith only [hx2L, hx3U]) (by linarith only [s10, hx3L]) (by linarith only [hc, hy3U]) (by linarith only [hy2U, s5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s12 : y2 ≤ (1612:ℝ) := le_of_not_gt fun hc =>
    cut7 (x2-x5) (y2-y5) 2584683 (-811:ℝ) (91:ℝ) (-1388:ℝ) (-843:ℝ) (657721:ℝ) (1926544:ℝ) hT25 (by linarith only [hx2L, s6]) (by linarith only [s10, hx5L]) (by linarith only [hc, hy5U]) (by linarith only [s11, hy5L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s13 : (1483:ℝ) ≤ x3 := le_of_not_gt fun hc =>
    cut7 (x2-x3) (y2-y3) 2584683 (-1483:ℝ) (-1335:ℝ) (-619:ℝ) (27:ℝ) (2199289:ℝ) (383161:ℝ) hT23 (by linarith only [hx2L, hc]) (by linarith only [s10, hx3L]) (by linarith only [s9, hy3U]) (by linarith only [s12, s5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s14 : (1708:ℝ) ≤ y3 := le_of_not_gt fun hc =>
    cut7 (x2-x3) (y2-y3) 2584683 (-1574:ℝ) (-1392:ℝ) (-327:ℝ) (27:ℝ) (2477476:ℝ) (106929:ℝ) hT23 (by linarith only [hx2L, hx3U]) (by linarith only [s10, s13]) (by linarith only [s9, hc]) (by linarith only [s12, s5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s15 : (1790:ℝ) ≤ y3 := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1517:ℝ) (-1278:ℝ) (235:ℝ) (532:ℝ) (2301289:ℝ) (283024:ℝ) hT34 (by linarith only [s13, hx4U]) (by linarith only [hx3U, hx4L]) (by linarith only [s14, s0]) (by linarith only [hc, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s16 : (2909:ℝ) ≤ x4 := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1426:ℝ) (-1278:ℝ) (317:ℝ) (742:ℝ) (2033476:ℝ) (550564:ℝ) hT34 (by linarith only [s13, hc]) (by linarith only [hx3U, hx4L]) (by linarith only [s15, s0]) (by linarith only [hy3U, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s17 : y4 ≤ (1468:ℝ) := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1517:ℝ) (-1335:ℝ) (317:ℝ) (532:ℝ) (2301289:ℝ) (283024:ℝ) hT34 (by linarith only [s13, hx4U]) (by linarith only [hx3U, s16]) (by linarith only [s15, s0]) (by linarith only [hy3U, hc]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s18 : (2769:ℝ) ≤ y5 := le_of_not_gt fun hc =>
    cut7 (x2-x5) (y2-y5) 2584683 (-811:ℝ) (91:ℝ) (-1388:ℝ) (-904:ℝ) (657721:ℝ) (1926544:ℝ) hT25 (by linarith only [hx2L, s6]) (by linarith only [s10, hx5L]) (by linarith only [s9, hc]) (by linarith only [s12, hy5L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s19 : x5 ≤ (516:ℝ) := le_of_not_gt fun hc =>
    cut7 (x3-x5) (y3-y5) 2584683 (672:ℝ) (1058:ℝ) (-1210:ℝ) (-769:ℝ) (1119364:ℝ) (1464100:ℝ) hT35 (by linarith only [s13, s6]) (by linarith only [hx3U, hc]) (by linarith only [s15, hy5U]) (by linarith only [hy3U, s18]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s22 : x0 ≤ (790:ℝ) := le_of_not_gt fun hc =>
    cut7 (x0-x1) (y0-y1) 2584683 (-1566:ℝ) (-1177:ℝ) (-215:ℝ) (361:ℝ) (2452356:ℝ) (130321:ℝ) hT01 (by linarith only [hc, s2]) (by linarith only [s7, hx1L]) (by linarith only [hy0L, s3]) (by linarith only [s8, hy1L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s23 : y0 ≤ (212:ℝ) := le_of_not_gt fun hc =>
    cut7 (x0-x2) (y0-y2) 2584683 (-91:ℝ) (790:ℝ) (-1400:ℝ) (-1020:ℝ) (624100:ℝ) (1960000:ℝ) hT02 (by linarith only [hx0L, s10]) (by linarith only [s22, hx2L]) (by linarith only [hc, s12]) (by linarith only [s8, s9]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s24 : x1 ≤ (2345:ℝ) := le_of_not_gt fun hc =>
    cut7 (x1-x4) (y1-y4) 2584683 (-655:ℝ) (-553:ℝ) (-1468:ℝ) (-1043:ℝ) (429025:ℝ) (2155024:ℝ) hT14 (by linarith only [hc, hx4U]) (by linarith only [s2, s16]) (by linarith only [hy1L, s17]) (by linarith only [s3, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s25 : y1 ≤ (210:ℝ) := le_of_not_gt fun hc =>
    cut7 (x1-x4) (y1-y4) 2584683 (-1000:ℝ) (-564:ℝ) (-1258:ℝ) (-1043:ℝ) (1000000:ℝ) (1582564:ℝ) hT14 (by linarith only [hx1L, hx4U]) (by linarith only [s24, s16]) (by linarith only [hc, s17]) (by linarith only [s3, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s26 : (1400:ℝ) ≤ y2 := le_of_not_gt fun hc =>
    cut7 (x0-x2) (y0-y2) 2584683 (-91:ℝ) (790:ℝ) (-1400:ℝ) (-1169:ℝ) (624100:ℝ) (1960000:ℝ) hT02 (by linarith only [hx0L, s10]) (by linarith only [s22, hx2L]) (by linarith only [hy0L, hc]) (by linarith only [s23, s9]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s27 : x2 ≤ (83:ℝ) := le_of_not_gt fun hc =>
    cut7 (x2-x3) (y2-y3) 2584683 (-1491:ℝ) (-1392:ℝ) (-600:ℝ) (-178:ℝ) (2223081:ℝ) (360000:ℝ) hT23 (by linarith only [hc, hx3U]) (by linarith only [s10, s13]) (by linarith only [s26, hy3U]) (by linarith only [s12, s15]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s28 : y2 ≤ (1478:ℝ) := le_of_not_gt fun hc =>
    cut7 (x2-x5) (y2-y5) 2584683 (-516:ℝ) (83:ℝ) (-1522:ℝ) (-1157:ℝ) (266256:ℝ) (2316484:ℝ) hT25 (by linarith only [hx2L, s19]) (by linarith only [s27, hx5L]) (by linarith only [hc, hy5U]) (by linarith only [s12, s18]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s29 : (1491:ℝ) ≤ x3 := le_of_not_gt fun hc =>
    cut7 (x2-x3) (y2-y3) 2584683 (-1491:ℝ) (-1400:ℝ) (-600:ℝ) (-312:ℝ) (2223081:ℝ) (360000:ℝ) hT23 (by linarith only [hx2L, hc]) (by linarith only [s27, s13]) (by linarith only [s26, hy3U]) (by linarith only [s28, s15]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s30 : (1812:ℝ) ≤ y3 := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1509:ℝ) (-1335:ℝ) (322:ℝ) (554:ℝ) (2277081:ℝ) (306916:ℝ) hT34 (by linarith only [s29, hx4U]) (by linarith only [hx3U, s16]) (by linarith only [s15, s17]) (by linarith only [hc, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s31 : (2917:ℝ) ≤ x4 := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1426:ℝ) (-1335:ℝ) (344:ℝ) (742:ℝ) (2033476:ℝ) (550564:ℝ) hT34 (by linarith only [s29, hc]) (by linarith only [hx3U, s16]) (by linarith only [s30, s17]) (by linarith only [hy3U, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s32 : y4 ≤ (1446:ℝ) := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1509:ℝ) (-1343:ℝ) (344:ℝ) (554:ℝ) (2277081:ℝ) (306916:ℝ) hT34 (by linarith only [s29, hx4U]) (by linarith only [hx3U, s31]) (by linarith only [s30, s17]) (by linarith only [hy3U, hc]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s33 : (157:ℝ) ≤ x5 := le_of_not_gt fun hc =>
    cut7 (x2-x5) (y2-y5) 2584683 (-157:ℝ) (83:ℝ) (-1600:ℝ) (-1291:ℝ) (24649:ℝ) (2560000:ℝ) hT25 (by linarith only [hx2L, hc]) (by linarith only [s27, hx5L]) (by linarith only [s26, hy5U]) (by linarith only [s28, s18]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s34 : (2922:ℝ) ≤ y5 := le_of_not_gt fun hc =>
    cut7 (x2-x5) (y2-y5) 2584683 (-516:ℝ) (-74:ℝ) (-1522:ℝ) (-1291:ℝ) (266256:ℝ) (2316484:ℝ) hT25 (by linarith only [hx2L, s19]) (by linarith only [s27, s33]) (by linarith only [s26, hc]) (by linarith only [s28, s18]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s35 : x5 ≤ (491:ℝ) := le_of_not_gt fun hc =>
    cut7 (x3-x5) (y3-y5) 2584683 (975:ℝ) (1083:ℝ) (-1188:ℝ) (-922:ℝ) (1172889:ℝ) (1411344:ℝ) hT35 (by linarith only [s29, s19]) (by linarith only [hx3U, hc]) (by linarith only [s30, hy5U]) (by linarith only [hy3U, s34]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s38 : x0 ≤ (752:ℝ) := le_of_not_gt fun hc =>
    cut7 (x0-x1) (y0-y1) 2584683 (-1593:ℝ) (-1210:ℝ) (-210:ℝ) (212:ℝ) (2537649:ℝ) (44944:ℝ) hT01 (by linarith only [hc, s24]) (by linarith only [s22, hx1L]) (by linarith only [hy0L, s25]) (by linarith only [s23, hy1L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s39 : (632:ℝ) ≤ x0 := le_of_not_gt fun hc =>
    cut7 (x0-x2) (y0-y2) 2584683 (-83:ℝ) (632:ℝ) (-1478:ℝ) (-1188:ℝ) (399424:ℝ) (2184484:ℝ) hT02 (by linarith only [hx0L, s27]) (by linarith only [hc, hx2L]) (by linarith only [hy0L, s28]) (by linarith only [s23, s26]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s40 : y0 ≤ (58:ℝ) := le_of_not_gt fun hc =>
    cut7 (x0-x2) (y0-y2) 2584683 (549:ℝ) (752:ℝ) (-1420:ℝ) (-1188:ℝ) (565504:ℝ) (2016400:ℝ) hT02 (by linarith only [s39, s27]) (by linarith only [s38, hx2L]) (by linarith only [hc, s28]) (by linarith only [s23, s26]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s41 : (2225:ℝ) ≤ x1 := le_of_not_gt fun hc =>
    cut7 (x0-x1) (y0-y1) 2584683 (-1593:ℝ) (-1248:ℝ) (-210:ℝ) (58:ℝ) (2537649:ℝ) (44100:ℝ) hT01 (by linarith only [s39, hc]) (by linarith only [s38, hx1L]) (by linarith only [hy0L, s25]) (by linarith only [s40, hy1L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s42 : x1 ≤ (2298:ℝ) := le_of_not_gt fun hc =>
    cut7 (x1-x4) (y1-y4) 2584683 (-702:ℝ) (-572:ℝ) (-1446:ℝ) (-1048:ℝ) (492804:ℝ) (2090916:ℝ) hT14 (by linarith only [hc, hx4U]) (by linarith only [s24, s31]) (by linarith only [hy1L, s32]) (by linarith only [s25, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s43 : y1 ≤ (38:ℝ) := le_of_not_gt fun hc =>
    cut7 (x1-x4) (y1-y4) 2584683 (-775:ℝ) (-619:ℝ) (-1408:ℝ) (-1048:ℝ) (600625:ℝ) (1982464:ℝ) hT14 (by linarith only [s41, hx4U]) (by linarith only [s42, s31]) (by linarith only [hc, s32]) (by linarith only [s25, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s44 : (1420:ℝ) ≤ y2 := le_of_not_gt fun hc =>
    cut7 (x0-x2) (y0-y2) 2584683 (549:ℝ) (752:ℝ) (-1420:ℝ) (-1342:ℝ) (565504:ℝ) (2016400:ℝ) hT02 (by linarith only [s39, s27]) (by linarith only [s38, hx2L]) (by linarith only [hy0L, hc]) (by linarith only [s40, s26]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s45 : x2 ≤ (75:ℝ) := le_of_not_gt fun hc =>
    cut7 (x2-x3) (y2-y3) 2584683 (-1499:ℝ) (-1408:ℝ) (-580:ℝ) (-334:ℝ) (2247001:ℝ) (336400:ℝ) hT23 (by linarith only [hc, hx3U]) (by linarith only [s27, s29]) (by linarith only [s44, hy3U]) (by linarith only [s28, s30]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s46 : y2 ≤ (1470:ℝ) := le_of_not_gt fun hc =>
    cut7 (x2-x5) (y2-y5) 2584683 (-491:ℝ) (-82:ℝ) (-1530:ℝ) (-1444:ℝ) (241081:ℝ) (2340900:ℝ) hT25 (by linarith only [hx2L, s35]) (by linarith only [s45, s33]) (by linarith only [hc, hy5U]) (by linarith only [s28, s34]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s47 : (1499:ℝ) ≤ x3 := le_of_not_gt fun hc =>
    cut7 (x2-x3) (y2-y3) 2584683 (-1499:ℝ) (-1416:ℝ) (-580:ℝ) (-342:ℝ) (2247001:ℝ) (336400:ℝ) hT23 (by linarith only [hx2L, hc]) (by linarith only [s45, s29]) (by linarith only [s44, hy3U]) (by linarith only [s46, s30]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s48 : (1833:ℝ) ≤ y3 := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1501:ℝ) (-1343:ℝ) (366:ℝ) (575:ℝ) (2253001:ℝ) (330625:ℝ) hT34 (by linarith only [s47, hx4U]) (by linarith only [hx3U, s31]) (by linarith only [s30, s32]) (by linarith only [hc, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s49 : (2927:ℝ) ≤ x4 := le_of_not_gt fun hc =>
    cut7 (x1-x4) (y1-y4) 2584683 (-702:ℝ) (-619:ℝ) (-1446:ℝ) (-1220:ℝ) (492804:ℝ) (2090916:ℝ) hT14 (by linarith only [s41, hc]) (by linarith only [s42, s31]) (by linarith only [hy1L, s32]) (by linarith only [s43, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s50 : (1408:ℝ) ≤ y4 := le_of_not_gt fun hc =>
    cut7 (x1-x4) (y1-y4) 2584683 (-775:ℝ) (-629:ℝ) (-1408:ℝ) (-1220:ℝ) (600625:ℝ) (1982464:ℝ) hT14 (by linarith only [s41, hx4U]) (by linarith only [s42, s49]) (by linarith only [hy1L, hc]) (by linarith only [s43, hy4L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s51 : (2993:ℝ) ≤ x4 := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1494:ℝ) (-1353:ℝ) (387:ℝ) (592:ℝ) (2232036:ℝ) (350464:ℝ) hT34 (by linarith only [s47, hc]) (by linarith only [hx3U, s49]) (by linarith only [s48, s32]) (by linarith only [hy3U, s50]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s52 : y4 ≤ (1425:ℝ) := le_of_not_gt fun hc =>
    cut7 (x3-x4) (y3-y4) 2584683 (-1501:ℝ) (-1419:ℝ) (387:ℝ) (575:ℝ) (2253001:ℝ) (330625:ℝ) hT34 (by linarith only [s47, hx4U]) (by linarith only [hx3U, s51]) (by linarith only [s48, s32]) (by linarith only [hy3U, hc]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s59 : x0 ≤ (692:ℝ) := le_of_not_gt fun hc =>
    cut7 (x0-x1) (y0-y1) 2584683 (-1606:ℝ) (-1473:ℝ) (-38:ℝ) (58:ℝ) (2579236:ℝ) (3364:ℝ) hT01 (by linarith only [hc, s42]) (by linarith only [s38, s41]) (by linarith only [hy0L, s43]) (by linarith only [s40, hy1L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s60 : (650:ℝ) ≤ x0 := le_of_not_gt fun hc =>
    cut7 (x0-x2) (y0-y2) 2584683 (557:ℝ) (650:ℝ) (-1470:ℝ) (-1362:ℝ) (422500:ℝ) (2160900:ℝ) hT02 (by linarith only [s39, s45]) (by linarith only [hc, hx2L]) (by linarith only [hy0L, s46]) (by linarith only [s40, s44]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s61 : y0 ≤ (19:ℝ) := le_of_not_gt fun hc =>
    cut7 (x0-x2) (y0-y2) 2584683 (575:ℝ) (692:ℝ) (-1451:ℝ) (-1362:ℝ) (478864:ℝ) (2105401:ℝ) hT02 (by linarith only [s60, s45]) (by linarith only [s59, hx2L]) (by linarith only [hc, s46]) (by linarith only [s40, s44]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s62 : (2257:ℝ) ≤ x1 := le_of_not_gt fun hc =>
    cut7 (x0-x1) (y0-y1) 2584683 (-1607:ℝ) (-1533:ℝ) (-38:ℝ) (19:ℝ) (2582449:ℝ) (1444:ℝ) hT01 (by linarith only [s60, hc]) (by linarith only [s59, s41]) (by linarith only [hy0L, s43]) (by linarith only [s61, hy1L]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (cut7 (x1-x4) (y1-y4) 2584683 (-743:ℝ) (-695:ℝ) (-1425:ℝ) (-1370:ℝ) (552049:ℝ) (2030625:ℝ) hT14 (by linarith only [s62, hx4U]) (by linarith only [s42, s51]) (by linarith only [hy1L, s52]) (by linarith only [s43, s50]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).elim
