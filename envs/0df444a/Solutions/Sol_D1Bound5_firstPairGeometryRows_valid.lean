-- Prove2me | solution 1 for D1Bound5.firstPairGeometryRows_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:47:54.403346+00:00
-- url     : https://prove2.me/submissions/cf56ed68-6abd-4e7c-8ae8-a86761101c84

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002
import Theorems.Thm_D1Bound5_firstPairGeometryRow_0_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_10_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_11_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_12_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_13_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_14_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_15_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_16_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_17_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_18_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_19_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_1_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_20_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_21_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_22_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_23_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_24_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_25_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_26_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_27_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_28_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_29_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_2_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_30_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_31_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_32_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_33_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_34_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_35_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_36_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_37_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_38_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_39_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_3_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_40_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_4_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_5_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_6_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_7_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_8_valid
import Theorems.Thm_D1Bound5_firstPairGeometryRow_9_valid

section
namespace D1Bound5
open QuadInt



namespace FirstPairGeometryRow






























end FirstPairGeometryRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000







































































































































































theorem _root_.solution (r : FirstPairGeometryRow)
    (hr : r ∈ firstPairGeometryRows) : r.Valid := by
  simp only [firstPairGeometryRows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact firstPairGeometryRow_0_valid
  · exact firstPairGeometryRow_1_valid
  · exact firstPairGeometryRow_2_valid
  · exact firstPairGeometryRow_3_valid
  · exact firstPairGeometryRow_4_valid
  · exact firstPairGeometryRow_5_valid
  · exact firstPairGeometryRow_6_valid
  · exact firstPairGeometryRow_7_valid
  · exact firstPairGeometryRow_8_valid
  · exact firstPairGeometryRow_9_valid
  · exact firstPairGeometryRow_10_valid
  · exact firstPairGeometryRow_11_valid
  · exact firstPairGeometryRow_12_valid
  · exact firstPairGeometryRow_13_valid
  · exact firstPairGeometryRow_14_valid
  · exact firstPairGeometryRow_15_valid
  · exact firstPairGeometryRow_16_valid
  · exact firstPairGeometryRow_17_valid
  · exact firstPairGeometryRow_18_valid
  · exact firstPairGeometryRow_19_valid
  · exact firstPairGeometryRow_20_valid
  · exact firstPairGeometryRow_21_valid
  · exact firstPairGeometryRow_22_valid
  · exact firstPairGeometryRow_23_valid
  · exact firstPairGeometryRow_24_valid
  · exact firstPairGeometryRow_25_valid
  · exact firstPairGeometryRow_26_valid
  · exact firstPairGeometryRow_27_valid
  · exact firstPairGeometryRow_28_valid
  · exact firstPairGeometryRow_29_valid
  · exact firstPairGeometryRow_30_valid
  · exact firstPairGeometryRow_31_valid
  · exact firstPairGeometryRow_32_valid
  · exact firstPairGeometryRow_33_valid
  · exact firstPairGeometryRow_34_valid
  · exact firstPairGeometryRow_35_valid
  · exact firstPairGeometryRow_36_valid
  · exact firstPairGeometryRow_37_valid
  · exact firstPairGeometryRow_38_valid
  · exact firstPairGeometryRow_39_valid
  · exact firstPairGeometryRow_40_valid























end D1Bound5
end
