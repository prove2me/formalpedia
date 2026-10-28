-- Prove2me | solution 1 for D1Bound5.firstPair_classified_rectangular
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:48:09.029375+00:00
-- url     : https://prove2.me/submissions/888bc07b-480f-42f6-b2aa-241298d3ca4f

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
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Theorems.Thm_D1Bound5_firstPair_classified_0_1
import Theorems.Thm_D1Bound5_firstPair_classified_0_2
import Theorems.Thm_D1Bound5_firstPair_classified_0_3
import Theorems.Thm_D1Bound5_firstPair_classified_0_4
import Theorems.Thm_D1Bound5_firstPair_classified_0_5
import Theorems.Thm_D1Bound5_firstPair_classified_0_6
import Theorems.Thm_D1Bound5_firstPair_classified_0_7
import Theorems.Thm_D1Bound5_firstPair_classified_0_8
import Theorems.Thm_D1Bound5_firstPair_classified_1_1
import Theorems.Thm_D1Bound5_firstPair_classified_1_2
import Theorems.Thm_D1Bound5_firstPair_classified_1_3
import Theorems.Thm_D1Bound5_firstPair_classified_1_4
import Theorems.Thm_D1Bound5_firstPair_classified_1_5
import Theorems.Thm_D1Bound5_firstPair_classified_1_6
import Theorems.Thm_D1Bound5_firstPair_classified_1_7
import Theorems.Thm_D1Bound5_firstPair_classified_1_8

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000













































































































































theorem _root_.solution {tau nu : ℤ}
    (htau : tau = 0 ∨ tau = 1) (hlo : 1 ≤ nu) (hhi : nu ≤ 8)
    (a b : QuadInt tau nu) (hnorm : FirstPairNorms a b) (hroot : ∃ q, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨ firstPairCoordinates a b ∈ firstPairTable tau nu := by
  rcases htau with rfl | rfl
  · interval_cases nu
    · exact firstPair_classified_0_1 a b hnorm hroot
    · exact firstPair_classified_0_2 a b hnorm hroot
    · exact firstPair_classified_0_3 a b hnorm hroot
    · exact firstPair_classified_0_4 a b hnorm hroot
    · exact firstPair_classified_0_5 a b hnorm hroot
    · exact firstPair_classified_0_6 a b hnorm hroot
    · exact firstPair_classified_0_7 a b hnorm hroot
    · exact firstPair_classified_0_8 a b hnorm hroot
  · interval_cases nu
    · exact firstPair_classified_1_1 a b hnorm hroot
    · exact firstPair_classified_1_2 a b hnorm hroot
    · exact firstPair_classified_1_3 a b hnorm hroot
    · exact firstPair_classified_1_4 a b hnorm hroot
    · exact firstPair_classified_1_5 a b hnorm hroot
    · exact firstPair_classified_1_6 a b hnorm hroot
    · exact firstPair_classified_1_7 a b hnorm hroot
    · exact firstPair_classified_1_8 a b hnorm hroot

end D1Bound5
end
