-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_17_root_hi_1_stage
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:16:49.703494+00:00
-- url     : https://prove2.me/submissions/5ed74260-02da-4d00-9e70-b266e3fc51d4

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

theorem solution (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
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
  have s0 : x0 ≤ (752:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x0-x1) (y0-y1) 2584683 (-1593:ℝ) (-1210:ℝ) (-210:ℝ) (212:ℝ) (2537649:ℝ) (44944:ℝ) hT01 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s1 : (632:ℝ) ≤ x0 := by
    by_contra hc; push_neg at hc
    exact cut7 (x0-x2) (y0-y2) 2584683 (-83:ℝ) (632:ℝ) (-1478:ℝ) (-1188:ℝ) (399424:ℝ) (2184484:ℝ) hT02 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2 : y0 ≤ (58:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x0-x2) (y0-y2) 2584683 (549:ℝ) (752:ℝ) (-1420:ℝ) (-1188:ℝ) (565504:ℝ) (2016400:ℝ) hT02 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s3 : (2225:ℝ) ≤ x1 := by
    by_contra hc; push_neg at hc
    exact cut7 (x0-x1) (y0-y1) 2584683 (-1593:ℝ) (-1248:ℝ) (-210:ℝ) (58:ℝ) (2537649:ℝ) (44100:ℝ) hT01 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4 : y1 ≤ (60:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x1-x4) (y1-y4) 2584683 (-775:ℝ) (-572:ℝ) (-1408:ℝ) (-1048:ℝ) (600625:ℝ) (1982464:ℝ) hT14 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s5 : (1420:ℝ) ≤ y2 := by
    by_contra hc; push_neg at hc
    exact cut7 (x0-x2) (y0-y2) 2584683 (549:ℝ) (752:ℝ) (-1420:ℝ) (-1342:ℝ) (565504:ℝ) (2016400:ℝ) hT02 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s6 : x2 ≤ (75:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x2-x3) (y2-y3) 2584683 (-1499:ℝ) (-1408:ℝ) (-580:ℝ) (-334:ℝ) (2247001:ℝ) (336400:ℝ) hT23 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s7 : (1499:ℝ) ≤ x3 := by
    by_contra hc; push_neg at hc
    exact cut7 (x2-x3) (y2-y3) 2584683 (-1499:ℝ) (-1416:ℝ) (-580:ℝ) (-334:ℝ) (2247001:ℝ) (336400:ℝ) hT23 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s8 : (1833:ℝ) ≤ y3 := by
    by_contra hc; push_neg at hc
    exact cut7 (x3-x4) (y3-y4) 2584683 (-1501:ℝ) (-1343:ℝ) (344:ℝ) (575:ℝ) (2253001:ℝ) (330625:ℝ) hT34 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s9 : (1408:ℝ) ≤ y4 := by
    by_contra hc; push_neg at hc
    exact cut7 (x1-x4) (y1-y4) 2584683 (-775:ℝ) (-572:ℝ) (-1408:ℝ) (-1198:ℝ) (600625:ℝ) (1982464:ℝ) hT14 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s10 : (2993:ℝ) ≤ x4 := by
    by_contra hc; push_neg at hc
    exact cut7 (x3-x4) (y3-y4) 2584683 (-1494:ℝ) (-1343:ℝ) (365:ℝ) (592:ℝ) (2232036:ℝ) (350464:ℝ) hT34 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s11 : y4 ≤ (1425:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x3-x4) (y3-y4) 2584683 (-1501:ℝ) (-1419:ℝ) (365:ℝ) (575:ℝ) (2253001:ℝ) (330625:ℝ) hT34 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s12 : (297:ℝ) ≤ x5 := by
    by_contra hc; push_neg at hc
    exact cut7 (x2-x5) (y2-y5) 2584683 (-297:ℝ) (75:ℝ) (-1580:ℝ) (-1291:ℝ) (88209:ℝ) (2496400:ℝ) hT25 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s13 : (2942:ℝ) ≤ y5 := by
    by_contra hc; push_neg at hc
    exact cut7 (x2-x5) (y2-y5) 2584683 (-516:ℝ) (-222:ℝ) (-1522:ℝ) (-1291:ℝ) (266256:ℝ) (2316484:ℝ) hT25 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s14 : x5 ≤ (469:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x3-x5) (y3-y5) 2584683 (983:ℝ) (1105:ℝ) (-1167:ℝ) (-942:ℝ) (1221025:ℝ) (1361889:ℝ) hT35 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s15 : (2604:ℝ) ≤ x6 := by
    by_contra hc; push_neg at hc
    exact cut7 (x3-x6) (y3-y6) 2584683 (-1105:ℝ) (-967:ℝ) (-1167:ℝ) (-798:ℝ) (1221025:ℝ) (1361889:ℝ) hT36 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s16 : x6 ≤ (2776:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x4-x6) (y4-y6) 2584683 (-7:ℝ) (224:ℝ) (-1592:ℝ) (-1373:ℝ) (50176:ℝ) (2534464:ℝ) hT46 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s17 : (2966:ℝ) ≤ y6 := by
    by_contra hc; push_neg at hc
    exact cut7 (x4-x6) (y4-y6) 2584683 (217:ℝ) (396:ℝ) (-1558:ℝ) (-1373:ℝ) (156816:ℝ) (2427364:ℝ) hT46 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s18 : x0 ≤ (739:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x0-x1) (y0-y1) 2584683 (-1606:ℝ) (-1473:ℝ) (-60:ℝ) (58:ℝ) (2579236:ℝ) (3600:ℝ) hT01 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s19 : y0 ≤ (51:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x0-x2) (y0-y2) 2584683 (557:ℝ) (739:ℝ) (-1427:ℝ) (-1362:ℝ) (546121:ℝ) (2036329:ℝ) hT02 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s20 : (2238:ℝ) ≤ x1 := by
    by_contra hc; push_neg at hc
    exact cut7 (x0-x1) (y0-y1) 2584683 (-1606:ℝ) (-1486:ℝ) (-60:ℝ) (51:ℝ) (2579236:ℝ) (3600:ℝ) hT01 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s21 : x1 ≤ (2256:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x1-x4) (y1-y4) 2584683 (-744:ℝ) (-648:ℝ) (-1425:ℝ) (-1348:ℝ) (553536:ℝ) (2030625:ℝ) hT14 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s22 : y1 ≤ (10:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x1-x4) (y1-y4) 2584683 (-762:ℝ) (-737:ℝ) (-1415:ℝ) (-1348:ℝ) (580644:ℝ) (2002225:ℝ) hT14 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s23 : (1427:ℝ) ≤ y2 := by
    by_contra hc; push_neg at hc
    exact cut7 (x0-x2) (y0-y2) 2584683 (557:ℝ) (739:ℝ) (-1427:ℝ) (-1369:ℝ) (546121:ℝ) (2036329:ℝ) hT02 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s24 : x2 ≤ (72:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x2-x3) (y2-y3) 2584683 (-1502:ℝ) (-1424:ℝ) (-573:ℝ) (-355:ℝ) (2256004:ℝ) (328329:ℝ) hT23 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s25 : y2 ≤ (1463:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x2-x5) (y2-y5) 2584683 (-469:ℝ) (-225:ℝ) (-1537:ℝ) (-1464:ℝ) (219961:ℝ) (2362369:ℝ) hT25 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s26 : (1502:ℝ) ≤ x3 := by
    by_contra hc; push_neg at hc
    exact cut7 (x2-x3) (y2-y3) 2584683 (-1502:ℝ) (-1427:ℝ) (-573:ℝ) (-370:ℝ) (2256004:ℝ) (328329:ℝ) hT23 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s27 : x3 ≤ (1506:ℝ) := by
    by_contra hc; push_neg at hc
    exact cut7 (x3-x4) (y3-y4) 2584683 (-1494:ℝ) (-1419:ℝ) (408:ℝ) (592:ℝ) (2232036:ℝ) (350464:ℝ) hT34 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s28 : (1991:ℝ) ≤ y3 := by
    by_contra hc; push_neg at hc
    exact cut7 (x3-x4) (y3-y4) 2584683 (-1498:ℝ) (-1487:ℝ) (408:ℝ) (583:ℝ) (2244004:ℝ) (339889:ℝ) hT34 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (cut7 (x3-x5) (y3-y5) 2584683 (1033:ℝ) (1209:ℝ) (-1009:ℝ) (-942:ℝ) (1461681:ℝ) (1018081:ℝ) hT35 (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).elim
