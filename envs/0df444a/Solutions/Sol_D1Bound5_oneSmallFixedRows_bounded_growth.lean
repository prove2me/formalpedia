-- Prove2me | solution 1 for D1Bound5.oneSmallFixedRows_bounded_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:41.712887+00:00
-- url     : https://prove2.me/submissions/fe0e149a-5284-46c2-91c3-0dc3299b6e37

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_oneSmallFourth_0_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_10_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_11_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_12_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_13_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_14_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_15_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_16_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_17_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_18_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_19_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_1_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_20_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_21_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_22_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_23_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_24_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_25_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_26_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_27_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_28_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_29_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_2_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_30_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_31_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_32_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_33_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_34_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_35_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_36_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_37_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_38_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_39_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_3_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_40_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_41_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_42_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_43_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_44_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_45_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_46_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_47_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_48_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_49_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_4_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_50_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_51_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_52_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_53_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_54_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_55_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_5_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_6_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_7_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_8_growth
import Theorems.Thm_D1Bound5_oneSmallFourth_9_growth

section
namespace D1Bound5
open QuadInt









/-- All 56 bounded complements are checked with exact integral roots.
Zero and anchor coincidences are allowed throughout this theorem. -/
theorem _root_.solution (r : OneSmallTripleRow)
    (hr : r ∈ oneSmallFixedRows) (z : QuadInt r.tau r.nu) (hz : z.norm < r.cutoff)
    (ha : ∃ q, q*q = r.anchorA*z+1) (hb : ∃ q, q*q = r.anchorB*z+1)
    (hs : ∃ q, q*q = r.anchorS*z+1) : z.norm ≤ 4*r.anchorB.norm*r.anchorS.norm := by
  simp only [oneSmallFixedRows, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oneSmallFourth_0_growth z hz ha hb hs
  · exact oneSmallFourth_1_growth z hz ha hb hs
  · exact oneSmallFourth_2_growth z hz ha hb hs
  · exact oneSmallFourth_3_growth z hz ha hb hs
  · exact oneSmallFourth_4_growth z hz ha hb hs
  · exact oneSmallFourth_5_growth z hz ha hb hs
  · exact oneSmallFourth_6_growth z hz ha hb hs
  · exact oneSmallFourth_7_growth z hz ha hb hs
  · exact oneSmallFourth_8_growth z hz ha hb hs
  · exact oneSmallFourth_9_growth z hz ha hb hs
  · exact oneSmallFourth_10_growth z hz ha hb hs
  · exact oneSmallFourth_11_growth z hz ha hb hs
  · exact oneSmallFourth_12_growth z hz ha hb hs
  · exact oneSmallFourth_13_growth z hz ha hb hs
  · exact oneSmallFourth_14_growth z hz ha hb hs
  · exact oneSmallFourth_15_growth z hz ha hb hs
  · exact oneSmallFourth_16_growth z hz ha hb hs
  · exact oneSmallFourth_17_growth z hz ha hb hs
  · exact oneSmallFourth_18_growth z hz ha hb hs
  · exact oneSmallFourth_19_growth z hz ha hb hs
  · exact oneSmallFourth_20_growth z hz ha hb hs
  · exact oneSmallFourth_21_growth z hz ha hb hs
  · exact oneSmallFourth_22_growth z hz ha hb hs
  · exact oneSmallFourth_23_growth z hz ha hb hs
  · exact oneSmallFourth_24_growth z hz ha hb hs
  · exact oneSmallFourth_25_growth z hz ha hb hs
  · exact oneSmallFourth_26_growth z hz ha hb hs
  · exact oneSmallFourth_27_growth z hz ha hb hs
  · exact oneSmallFourth_28_growth z hz ha hb hs
  · exact oneSmallFourth_29_growth z hz ha hb hs
  · exact oneSmallFourth_30_growth z hz ha hb hs
  · exact oneSmallFourth_31_growth z hz ha hb hs
  · exact oneSmallFourth_32_growth z hz ha hb hs
  · exact oneSmallFourth_33_growth z hz ha hb hs
  · exact oneSmallFourth_34_growth z hz ha hb hs
  · exact oneSmallFourth_35_growth z hz ha hb hs
  · exact oneSmallFourth_36_growth z hz ha hb hs
  · exact oneSmallFourth_37_growth z hz ha hb hs
  · exact oneSmallFourth_38_growth z hz ha hb hs
  · exact oneSmallFourth_39_growth z hz ha hb hs
  · exact oneSmallFourth_40_growth z hz ha hb hs
  · exact oneSmallFourth_41_growth z hz ha hb hs
  · exact oneSmallFourth_42_growth z hz ha hb hs
  · exact oneSmallFourth_43_growth z hz ha hb hs
  · exact oneSmallFourth_44_growth z hz ha hb hs
  · exact oneSmallFourth_45_growth z hz ha hb hs
  · exact oneSmallFourth_46_growth z hz ha hb hs
  · exact oneSmallFourth_47_growth z hz ha hb hs
  · exact oneSmallFourth_48_growth z hz ha hb hs
  · exact oneSmallFourth_49_growth z hz ha hb hs
  · exact oneSmallFourth_50_growth z hz ha hb hs
  · exact oneSmallFourth_51_growth z hz ha hb hs
  · exact oneSmallFourth_52_growth z hz ha hb hs
  · exact oneSmallFourth_53_growth z hz ha hb hs
  · exact oneSmallFourth_54_growth z hz ha hb hs
  · exact oneSmallFourth_55_growth z hz ha hb hs





















































































end D1Bound5
end
