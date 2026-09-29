-- Prove2me | solution 1 for CirclePackingConstants.n7_pattern_17_low_high_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:36:56.897986+00:00
-- url     : https://prove2.me/submissions/ca687802-4d5e-41be-85c3-8329e376e690

import Theorems.Thm_CirclePackingConstants_n7_pattern_17_root_0_stage
import Theorems.Thm_CirclePackingConstants_n7_pattern_17_root_lo_0_stage
import Theorems.Thm_CirclePackingConstants_n7_pattern_17_root_lo_hi_0_stage
import Theorems.Thm_CirclePackingConstants_n7_pattern_17_root_lo_hi_1_stage
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

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
  (hsplit1 : (2500:ℝ) ≤ x1)
  : False   := by
  have hs0 := CirclePackingConstants.n7_pattern_17_root_0_stage x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 hx0L hx0U hy0L hy0U hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56
  rcases hs0 with
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27⟩
  have hs1 := CirclePackingConstants.n7_pattern_17_root_lo_0_stage x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 hsplit0 a26 a27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56
  rcases hs1 with
    ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27⟩
  have hs2 := CirclePackingConstants.n7_pattern_17_root_lo_hi_0_stage x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 b0 b1 b2 b3 hsplit1 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56
  rcases hs2 with
    ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27⟩
  have hs3 := CirclePackingConstants.n7_pattern_17_root_lo_hi_1_stage x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56
  rcases hs3 with
    ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27⟩
  have dxlo : -(1577:ℝ) ≤ x6-x5 := by linarith [c24, c21]
  have dxhi : x6-x5 ≤ (1577:ℝ) := by linarith [c25, c20]
  have dxp : 0 ≤ (1577:ℝ) - (x6-x5) := by linarith
  have dxm : 0 ≤ (1577:ℝ) + (x6-x5) := by linarith
  have dx : (x6-x5)^2 ≤ (1577:ℝ)^2 := by
    nlinarith only [mul_nonneg dxp dxm]
  have dylo : -(36:ℝ) ≤ y6-y5 := by linarith [c26, c23]
  have dyhi : y6-y5 ≤ (36:ℝ) := by linarith [c27, c22]
  have dyp : 0 ≤ (36:ℝ) - (y6-y5) := by linarith
  have dym : 0 ≤ (36:ℝ) + (y6-y5) := by linarith
  have dy : (y6-y5)^2 ≤ (36:ℝ)^2 := by
    nlinarith only [mul_nonneg dyp dym]
  have hc : (1577:ℝ)^2 + (36:ℝ)^2 < 2584683 := by norm_num
  nlinarith only [hT56, dx, dy, hc]
