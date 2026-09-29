-- Prove2me | solution 1 for CirclePackingConstants.n7_rep13_localization
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T00:56:04.189989+00:00
-- url     : https://prove2.me/submissions/8356a87d-57a6-4933-814a-687b3f0d6e0a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_0
import Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_1
import Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_2
import Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_3
import Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_4
import Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_5
import Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_6
import Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_7

theorem solution
 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L : (0:ℝ) ≤ x0)
 (hx0U : x0 ≤ (1000:ℝ))
 (hy0L : (0:ℝ) ≤ y0)
 (hy0U : y0 ≤ (1000:ℝ))
 (hx1L : (2000:ℝ) ≤ x1)
 (hx1U : x1 ≤ (3000:ℝ))
 (hy1L : (0:ℝ) ≤ y1)
 (hy1U : y1 ≤ (1000:ℝ))
 (hx2L : (1000:ℝ) ≤ x2)
 (hx2U : x2 ≤ (2000:ℝ))
 (hy2L : (1000:ℝ) ≤ y2)
 (hy2U : y2 ≤ (2000:ℝ))
 (hx3L : (2000:ℝ) ≤ x3)
 (hx3U : x3 ≤ (3000:ℝ))
 (hy3L : (1000:ℝ) ≤ y3)
 (hy3U : y3 ≤ (2000:ℝ))
 (hx4L : (0:ℝ) ≤ x4)
 (hx4U : x4 ≤ (1000:ℝ))
 (hy4L : (2000:ℝ) ≤ y4)
 (hy4U : y4 ≤ (3000:ℝ))
 (hx5L : (1000:ℝ) ≤ x5)
 (hx5U : x5 ≤ (2000:ℝ))
 (hy5L : (2000:ℝ) ≤ y5)
 (hy5U : y5 ≤ (3000:ℝ))
 (hx6L : (2000:ℝ) ≤ x6)
 (hx6U : x6 ≤ (3000:ℝ))
 (hy6L : (2000:ℝ) ≤ y6)
 (hy6U : y6 ≤ (3000:ℝ))
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
 : (0:ℝ) ≤ x0 ∧ x0 ≤ (591:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (591:ℝ) ∧ (2190:ℝ) ≤ x1 ∧ x1 ≤ (2198:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (5:ℝ) ∧ (1388:ℝ) ≤ x2 ∧ x2 ≤ (1393:ℝ) ∧ (1388:ℝ) ≤ y2 ∧ y2 ≤ (1393:ℝ) ∧ (2995:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1388:ℝ) ≤ y3 ∧ y3 ≤ (1393:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (5:ℝ) ∧ (2190:ℝ) ≤ y4 ∧ y4 ≤ (2198:ℝ) ∧ (1388:ℝ) ≤ x5 ∧ x5 ≤ (1393:ℝ) ∧ (2995:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2995:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2995:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ)  := by
  rcases CirclePackingConstants.n7_rep13_interval_stage_0 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 hx0L hx0U hy0L hy0U hx1L hx1U hy1L hy1U hx2L hx2U hy2L hy2U hx3L hx3U hy3L hy3U hx4L hx4U hy4L hy4U hx5L hx5U hy5L hy5U hx6L hx6U hy6L hy6U hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6, s0_7, s0_8, s0_9, s0_10, s0_11, s0_12, s0_13, s0_14, s0_15, s0_16, s0_17, s0_18, s0_19, s0_20, s0_21, s0_22, s0_23, s0_24, s0_25, s0_26, s0_27⟩
  rcases CirclePackingConstants.n7_rep13_interval_stage_1 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 s0_0 s0_1 s0_2 s0_3 s0_4 s0_5 s0_6 s0_7 s0_8 s0_9 s0_10 s0_11 s0_12 s0_13 s0_14 s0_15 s0_16 s0_17 s0_18 s0_19 s0_20 s0_21 s0_22 s0_23 s0_24 s0_25 s0_26 s0_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6, s1_7, s1_8, s1_9, s1_10, s1_11, s1_12, s1_13, s1_14, s1_15, s1_16, s1_17, s1_18, s1_19, s1_20, s1_21, s1_22, s1_23, s1_24, s1_25, s1_26, s1_27⟩
  rcases CirclePackingConstants.n7_rep13_interval_stage_2 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 s1_0 s1_1 s1_2 s1_3 s1_4 s1_5 s1_6 s1_7 s1_8 s1_9 s1_10 s1_11 s1_12 s1_13 s1_14 s1_15 s1_16 s1_17 s1_18 s1_19 s1_20 s1_21 s1_22 s1_23 s1_24 s1_25 s1_26 s1_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨s2_0, s2_1, s2_2, s2_3, s2_4, s2_5, s2_6, s2_7, s2_8, s2_9, s2_10, s2_11, s2_12, s2_13, s2_14, s2_15, s2_16, s2_17, s2_18, s2_19, s2_20, s2_21, s2_22, s2_23, s2_24, s2_25, s2_26, s2_27⟩
  rcases CirclePackingConstants.n7_rep13_interval_stage_3 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 s2_0 s2_1 s2_2 s2_3 s2_4 s2_5 s2_6 s2_7 s2_8 s2_9 s2_10 s2_11 s2_12 s2_13 s2_14 s2_15 s2_16 s2_17 s2_18 s2_19 s2_20 s2_21 s2_22 s2_23 s2_24 s2_25 s2_26 s2_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨s3_0, s3_1, s3_2, s3_3, s3_4, s3_5, s3_6, s3_7, s3_8, s3_9, s3_10, s3_11, s3_12, s3_13, s3_14, s3_15, s3_16, s3_17, s3_18, s3_19, s3_20, s3_21, s3_22, s3_23, s3_24, s3_25, s3_26, s3_27⟩
  rcases CirclePackingConstants.n7_rep13_interval_stage_4 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 s3_0 s3_1 s3_2 s3_3 s3_4 s3_5 s3_6 s3_7 s3_8 s3_9 s3_10 s3_11 s3_12 s3_13 s3_14 s3_15 s3_16 s3_17 s3_18 s3_19 s3_20 s3_21 s3_22 s3_23 s3_24 s3_25 s3_26 s3_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨s4_0, s4_1, s4_2, s4_3, s4_4, s4_5, s4_6, s4_7, s4_8, s4_9, s4_10, s4_11, s4_12, s4_13, s4_14, s4_15, s4_16, s4_17, s4_18, s4_19, s4_20, s4_21, s4_22, s4_23, s4_24, s4_25, s4_26, s4_27⟩
  rcases CirclePackingConstants.n7_rep13_interval_stage_5 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 s4_0 s4_1 s4_2 s4_3 s4_4 s4_5 s4_6 s4_7 s4_8 s4_9 s4_10 s4_11 s4_12 s4_13 s4_14 s4_15 s4_16 s4_17 s4_18 s4_19 s4_20 s4_21 s4_22 s4_23 s4_24 s4_25 s4_26 s4_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨s5_0, s5_1, s5_2, s5_3, s5_4, s5_5, s5_6, s5_7, s5_8, s5_9, s5_10, s5_11, s5_12, s5_13, s5_14, s5_15, s5_16, s5_17, s5_18, s5_19, s5_20, s5_21, s5_22, s5_23, s5_24, s5_25, s5_26, s5_27⟩
  rcases CirclePackingConstants.n7_rep13_interval_stage_6 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 s5_0 s5_1 s5_2 s5_3 s5_4 s5_5 s5_6 s5_7 s5_8 s5_9 s5_10 s5_11 s5_12 s5_13 s5_14 s5_15 s5_16 s5_17 s5_18 s5_19 s5_20 s5_21 s5_22 s5_23 s5_24 s5_25 s5_26 s5_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨s6_0, s6_1, s6_2, s6_3, s6_4, s6_5, s6_6, s6_7, s6_8, s6_9, s6_10, s6_11, s6_12, s6_13, s6_14, s6_15, s6_16, s6_17, s6_18, s6_19, s6_20, s6_21, s6_22, s6_23, s6_24, s6_25, s6_26, s6_27⟩
  rcases CirclePackingConstants.n7_rep13_interval_stage_7 x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 s6_0 s6_1 s6_2 s6_3 s6_4 s6_5 s6_6 s6_7 s6_8 s6_9 s6_10 s6_11 s6_12 s6_13 s6_14 s6_15 s6_16 s6_17 s6_18 s6_19 s6_20 s6_21 s6_22 s6_23 s6_24 s6_25 s6_26 s6_27 hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56 with
    ⟨s7_0, s7_1, s7_2, s7_3, s7_4, s7_5, s7_6, s7_7, s7_8, s7_9, s7_10, s7_11, s7_12, s7_13, s7_14, s7_15, s7_16, s7_17, s7_18, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27⟩
  exact ⟨s7_0, s7_1, s7_2, s7_3, s7_4, s7_5, s7_6, s7_7, s7_8, s7_9, s7_10, s7_11, s7_12, s7_13, s7_14, s7_15, s7_16, s7_17, s7_18, s7_19, s7_20, s7_21, s7_22, s7_23, s7_24, s7_25, s7_26, s7_27⟩
