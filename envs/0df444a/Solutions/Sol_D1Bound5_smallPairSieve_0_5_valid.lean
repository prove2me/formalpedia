-- Prove2me | solution 1 for D1Bound5.smallPairSieve_0_5_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:40:47.361975+00:00
-- url     : https://prove2.me/submissions/6a1337d4-d2b2-44a1-bb25-a1527a96c18f

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_5_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_cons
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_nil
import Theorems.Thm_D1Bound5_smallPairMask_0_5_0_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_10_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_11_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_12_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_13_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_14_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_15_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_16_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_17_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_18_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_19_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_1_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_20_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_21_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_22_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_23_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_24_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_2_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_3_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_4_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_5_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_6_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_7_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_8_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_5_9_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.solution : CoordinateSquareSieveValid 0 5 smallPairSieve_0_5 := by
  exact
    coordinateSquareSieveValid_cons smallPairMask_0_5_0_valid (
      coordinateSquareSieveValid_cons smallPairMask_0_5_1_valid (
        coordinateSquareSieveValid_cons smallPairMask_0_5_2_valid (
          coordinateSquareSieveValid_cons smallPairMask_0_5_3_valid (
            coordinateSquareSieveValid_cons smallPairMask_0_5_4_valid (
              coordinateSquareSieveValid_cons smallPairMask_0_5_5_valid (
                coordinateSquareSieveValid_cons smallPairMask_0_5_6_valid (
                  coordinateSquareSieveValid_cons smallPairMask_0_5_7_valid (
                    coordinateSquareSieveValid_cons smallPairMask_0_5_8_valid (
                      coordinateSquareSieveValid_cons smallPairMask_0_5_9_valid (
                        coordinateSquareSieveValid_cons smallPairMask_0_5_10_valid (
                          coordinateSquareSieveValid_cons smallPairMask_0_5_11_valid (
                            coordinateSquareSieveValid_cons smallPairMask_0_5_12_valid (
                              coordinateSquareSieveValid_cons smallPairMask_0_5_13_valid (
                                coordinateSquareSieveValid_cons smallPairMask_0_5_14_valid (
                                  coordinateSquareSieveValid_cons smallPairMask_0_5_15_valid (
                                    coordinateSquareSieveValid_cons smallPairMask_0_5_16_valid (
                                      coordinateSquareSieveValid_cons smallPairMask_0_5_17_valid (
                                        coordinateSquareSieveValid_cons smallPairMask_0_5_18_valid (
                                          coordinateSquareSieveValid_cons smallPairMask_0_5_19_valid (
                                            coordinateSquareSieveValid_cons smallPairMask_0_5_20_valid (
                                              coordinateSquareSieveValid_cons smallPairMask_0_5_21_valid (
                                                coordinateSquareSieveValid_cons smallPairMask_0_5_22_valid (
                                                  coordinateSquareSieveValid_cons smallPairMask_0_5_23_valid (
                                                    coordinateSquareSieveValid_cons smallPairMask_0_5_24_valid (
                                                      coordinateSquareSieveValid_nil 0 5)))))))))))))))))))))))))

end D1Bound5
end
