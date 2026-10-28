-- Prove2me | solution 1 for D1Bound5.smallTailCheck_rectangular
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:25:40.11899+00:00
-- url     : https://prove2.me/submissions/ca67ed71-5c8d-44af-8bab-e2c7297410a6

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
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_FiniteTail_Definitions
import Definitions.Def_D1Bound5_SmallTailAllData_Definitions
import Definitions.Def_D1Bound5_SmallTailData0_1_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_smallTailCheck_of_explicit_list
import Theorems.Thm_D1Bound5_small_tail_015_no_small_third
import Theorems.Thm_D1Bound5_small_tail_015_pair_cases
import Theorems.Thm_D1Bound5_tailDisk_0_10_checked
import Theorems.Thm_D1Bound5_tailDisk_0_10_eq
import Theorems.Thm_D1Bound5_tailDisk_0_11_checked
import Theorems.Thm_D1Bound5_tailDisk_0_11_eq
import Theorems.Thm_D1Bound5_tailDisk_0_12_checked
import Theorems.Thm_D1Bound5_tailDisk_0_12_eq
import Theorems.Thm_D1Bound5_tailDisk_0_13_checked
import Theorems.Thm_D1Bound5_tailDisk_0_13_eq
import Theorems.Thm_D1Bound5_tailDisk_0_14_checked
import Theorems.Thm_D1Bound5_tailDisk_0_14_eq
import Theorems.Thm_D1Bound5_tailDisk_0_1_checked
import Theorems.Thm_D1Bound5_tailDisk_0_1_eq
import Theorems.Thm_D1Bound5_tailDisk_0_2_checked
import Theorems.Thm_D1Bound5_tailDisk_0_2_eq
import Theorems.Thm_D1Bound5_tailDisk_0_3_checked
import Theorems.Thm_D1Bound5_tailDisk_0_3_eq
import Theorems.Thm_D1Bound5_tailDisk_0_4_checked
import Theorems.Thm_D1Bound5_tailDisk_0_4_eq
import Theorems.Thm_D1Bound5_tailDisk_0_5_checked
import Theorems.Thm_D1Bound5_tailDisk_0_5_eq
import Theorems.Thm_D1Bound5_tailDisk_0_6_checked
import Theorems.Thm_D1Bound5_tailDisk_0_6_eq
import Theorems.Thm_D1Bound5_tailDisk_0_7_checked
import Theorems.Thm_D1Bound5_tailDisk_0_7_eq
import Theorems.Thm_D1Bound5_tailDisk_0_8_checked
import Theorems.Thm_D1Bound5_tailDisk_0_8_eq
import Theorems.Thm_D1Bound5_tailDisk_0_9_checked
import Theorems.Thm_D1Bound5_tailDisk_0_9_eq
import Theorems.Thm_D1Bound5_tailDisk_1_10_checked
import Theorems.Thm_D1Bound5_tailDisk_1_10_eq
import Theorems.Thm_D1Bound5_tailDisk_1_11_checked
import Theorems.Thm_D1Bound5_tailDisk_1_11_eq
import Theorems.Thm_D1Bound5_tailDisk_1_12_checked
import Theorems.Thm_D1Bound5_tailDisk_1_12_eq
import Theorems.Thm_D1Bound5_tailDisk_1_13_checked
import Theorems.Thm_D1Bound5_tailDisk_1_13_eq
import Theorems.Thm_D1Bound5_tailDisk_1_14_checked
import Theorems.Thm_D1Bound5_tailDisk_1_14_eq
import Theorems.Thm_D1Bound5_tailDisk_1_15_checked
import Theorems.Thm_D1Bound5_tailDisk_1_15_eq
import Theorems.Thm_D1Bound5_tailDisk_1_1_checked
import Theorems.Thm_D1Bound5_tailDisk_1_1_eq
import Theorems.Thm_D1Bound5_tailDisk_1_2_checked
import Theorems.Thm_D1Bound5_tailDisk_1_2_eq
import Theorems.Thm_D1Bound5_tailDisk_1_3_checked
import Theorems.Thm_D1Bound5_tailDisk_1_3_eq
import Theorems.Thm_D1Bound5_tailDisk_1_4_checked
import Theorems.Thm_D1Bound5_tailDisk_1_4_eq
import Theorems.Thm_D1Bound5_tailDisk_1_5_checked
import Theorems.Thm_D1Bound5_tailDisk_1_5_eq
import Theorems.Thm_D1Bound5_tailDisk_1_6_checked
import Theorems.Thm_D1Bound5_tailDisk_1_6_eq
import Theorems.Thm_D1Bound5_tailDisk_1_7_checked
import Theorems.Thm_D1Bound5_tailDisk_1_7_eq
import Theorems.Thm_D1Bound5_tailDisk_1_8_checked
import Theorems.Thm_D1Bound5_tailDisk_1_8_eq
import Theorems.Thm_D1Bound5_tailDisk_1_9_checked
import Theorems.Thm_D1Bound5_tailDisk_1_9_eq

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000







theorem smallTailExplicit_0_1 : SmallTailCheck 0 1 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_1
  · intro z hz
    rw [tailDisk_0_1_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_1_checked

end D1Bound5
end

section
namespace D1Bound5
open QuadInt

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000





/-- Fully discharged finite-tail certificate for the quadratic order
Z[sqrt(-15)]. This uses kernel reduction on two small finite statements. -/
theorem small_tail_015 : SmallTailCheck 0 15 := by
  intro b hb c hc h9 hbc hne hsq d hd hd0 hdb hdc hcd
    a ha ha0 hab hac had hNa hsab hsac
  rcases small_tail_015_pair_cases b hb c hc h9 hbc hne hsq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := small_tail_015_no_small_third a ha ha0
    simp [hsab, hsac] at h
  · have h := small_tail_015_no_small_third a ha ha0
    simp [hsab, hsac] at h

end D1Bound5
end

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000







theorem smallTailExplicit_0_2 : SmallTailCheck 0 2 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_2
  · intro z hz
    rw [tailDisk_0_2_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_2_checked







theorem smallTailExplicit_0_3 : SmallTailCheck 0 3 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_3
  · intro z hz
    rw [tailDisk_0_3_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_3_checked







theorem smallTailExplicit_0_4 : SmallTailCheck 0 4 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_4
  · intro z hz
    rw [tailDisk_0_4_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_4_checked







theorem smallTailExplicit_0_5 : SmallTailCheck 0 5 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_5
  · intro z hz
    rw [tailDisk_0_5_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_5_checked







theorem smallTailExplicit_0_6 : SmallTailCheck 0 6 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_6
  · intro z hz
    rw [tailDisk_0_6_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_6_checked







theorem smallTailExplicit_0_7 : SmallTailCheck 0 7 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_7
  · intro z hz
    rw [tailDisk_0_7_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_7_checked







theorem smallTailExplicit_0_8 : SmallTailCheck 0 8 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_8
  · intro z hz
    rw [tailDisk_0_8_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_8_checked







theorem smallTailExplicit_0_9 : SmallTailCheck 0 9 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_9
  · intro z hz
    rw [tailDisk_0_9_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_9_checked







theorem smallTailExplicit_0_10 : SmallTailCheck 0 10 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_10
  · intro z hz
    rw [tailDisk_0_10_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_10_checked







theorem smallTailExplicit_0_11 : SmallTailCheck 0 11 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_11
  · intro z hz
    rw [tailDisk_0_11_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_11_checked







theorem smallTailExplicit_0_12 : SmallTailCheck 0 12 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_12
  · intro z hz
    rw [tailDisk_0_12_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_12_checked







theorem smallTailExplicit_0_13 : SmallTailCheck 0 13 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_13
  · intro z hz
    rw [tailDisk_0_13_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_13_checked







theorem smallTailExplicit_0_14 : SmallTailCheck 0 14 := by
  apply smallTailCheck_of_explicit_list tailDisk_0_14
  · intro z hz
    rw [tailDisk_0_14_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_0_14_checked







theorem smallTailExplicit_1_1 : SmallTailCheck 1 1 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_1
  · intro z hz
    rw [tailDisk_1_1_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_1_checked







theorem smallTailExplicit_1_2 : SmallTailCheck 1 2 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_2
  · intro z hz
    rw [tailDisk_1_2_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_2_checked







theorem smallTailExplicit_1_3 : SmallTailCheck 1 3 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_3
  · intro z hz
    rw [tailDisk_1_3_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_3_checked







theorem smallTailExplicit_1_4 : SmallTailCheck 1 4 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_4
  · intro z hz
    rw [tailDisk_1_4_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_4_checked







theorem smallTailExplicit_1_5 : SmallTailCheck 1 5 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_5
  · intro z hz
    rw [tailDisk_1_5_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_5_checked







theorem smallTailExplicit_1_6 : SmallTailCheck 1 6 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_6
  · intro z hz
    rw [tailDisk_1_6_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_6_checked







theorem smallTailExplicit_1_7 : SmallTailCheck 1 7 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_7
  · intro z hz
    rw [tailDisk_1_7_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_7_checked







theorem smallTailExplicit_1_8 : SmallTailCheck 1 8 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_8
  · intro z hz
    rw [tailDisk_1_8_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_8_checked







theorem smallTailExplicit_1_9 : SmallTailCheck 1 9 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_9
  · intro z hz
    rw [tailDisk_1_9_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_9_checked







theorem smallTailExplicit_1_10 : SmallTailCheck 1 10 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_10
  · intro z hz
    rw [tailDisk_1_10_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_10_checked







theorem smallTailExplicit_1_11 : SmallTailCheck 1 11 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_11
  · intro z hz
    rw [tailDisk_1_11_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_11_checked







theorem smallTailExplicit_1_12 : SmallTailCheck 1 12 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_12
  · intro z hz
    rw [tailDisk_1_12_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_12_checked







theorem smallTailExplicit_1_13 : SmallTailCheck 1 13 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_13
  · intro z hz
    rw [tailDisk_1_13_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_13_checked







theorem smallTailExplicit_1_14 : SmallTailCheck 1 14 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_14
  · intro z hz
    rw [tailDisk_1_14_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_14_checked







theorem smallTailExplicit_1_15 : SmallTailCheck 1 15 := by
  apply smallTailCheck_of_explicit_list tailDisk_1_15
  · intro z hz
    rw [tailDisk_1_15_eq, List.mem_toFinset] at hz
    exact hz
  · exact tailDisk_1_15_checked

/-- Complete finite certificate for the normalized parameter rectangle.
Every data equality and every exclusion above is checked by the kernel. -/
theorem _root_.solution (tau nu : ℤ)
    (htau : tau = 0 ∨ tau = 1) (hlo : 1 ≤ nu) (hhi : nu ≤ 15)
    (_hpos : 0 < discriminant tau nu) : SmallTailCheck tau nu := by
  rcases htau with rfl | rfl
  · interval_cases nu
    · exact smallTailExplicit_0_1
    · exact smallTailExplicit_0_2
    · exact smallTailExplicit_0_3
    · exact smallTailExplicit_0_4
    · exact smallTailExplicit_0_5
    · exact smallTailExplicit_0_6
    · exact smallTailExplicit_0_7
    · exact smallTailExplicit_0_8
    · exact smallTailExplicit_0_9
    · exact smallTailExplicit_0_10
    · exact smallTailExplicit_0_11
    · exact smallTailExplicit_0_12
    · exact smallTailExplicit_0_13
    · exact smallTailExplicit_0_14
    · exact small_tail_015
  · interval_cases nu
    · exact smallTailExplicit_1_1
    · exact smallTailExplicit_1_2
    · exact smallTailExplicit_1_3
    · exact smallTailExplicit_1_4
    · exact smallTailExplicit_1_5
    · exact smallTailExplicit_1_6
    · exact smallTailExplicit_1_7
    · exact smallTailExplicit_1_8
    · exact smallTailExplicit_1_9
    · exact smallTailExplicit_1_10
    · exact smallTailExplicit_1_11
    · exact smallTailExplicit_1_12
    · exact smallTailExplicit_1_13
    · exact smallTailExplicit_1_14
    · exact smallTailExplicit_1_15

end D1Bound5
end
