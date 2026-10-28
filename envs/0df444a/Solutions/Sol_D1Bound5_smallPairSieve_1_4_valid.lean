-- Prove2me | solution 1 for D1Bound5.smallPairSieve_1_4_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:40:50.045055+00:00
-- url     : https://prove2.me/submissions/f5b72b9c-0e12-4b94-9520-7e0e5e933082

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_4_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_cons
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_nil
import Theorems.Thm_D1Bound5_smallPairMask_1_4_0_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_10_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_11_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_12_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_13_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_14_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_15_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_16_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_17_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_18_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_19_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_1_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_20_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_21_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_22_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_23_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_24_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_2_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_3_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_4_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_5_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_6_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_7_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_8_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_4_9_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.solution : CoordinateSquareSieveValid 1 4 smallPairSieve_1_4 := by
  exact
    coordinateSquareSieveValid_cons smallPairMask_1_4_0_valid (
      coordinateSquareSieveValid_cons smallPairMask_1_4_1_valid (
        coordinateSquareSieveValid_cons smallPairMask_1_4_2_valid (
          coordinateSquareSieveValid_cons smallPairMask_1_4_3_valid (
            coordinateSquareSieveValid_cons smallPairMask_1_4_4_valid (
              coordinateSquareSieveValid_cons smallPairMask_1_4_5_valid (
                coordinateSquareSieveValid_cons smallPairMask_1_4_6_valid (
                  coordinateSquareSieveValid_cons smallPairMask_1_4_7_valid (
                    coordinateSquareSieveValid_cons smallPairMask_1_4_8_valid (
                      coordinateSquareSieveValid_cons smallPairMask_1_4_9_valid (
                        coordinateSquareSieveValid_cons smallPairMask_1_4_10_valid (
                          coordinateSquareSieveValid_cons smallPairMask_1_4_11_valid (
                            coordinateSquareSieveValid_cons smallPairMask_1_4_12_valid (
                              coordinateSquareSieveValid_cons smallPairMask_1_4_13_valid (
                                coordinateSquareSieveValid_cons smallPairMask_1_4_14_valid (
                                  coordinateSquareSieveValid_cons smallPairMask_1_4_15_valid (
                                    coordinateSquareSieveValid_cons smallPairMask_1_4_16_valid (
                                      coordinateSquareSieveValid_cons smallPairMask_1_4_17_valid (
                                        coordinateSquareSieveValid_cons smallPairMask_1_4_18_valid (
                                          coordinateSquareSieveValid_cons smallPairMask_1_4_19_valid (
                                            coordinateSquareSieveValid_cons smallPairMask_1_4_20_valid (
                                              coordinateSquareSieveValid_cons smallPairMask_1_4_21_valid (
                                                coordinateSquareSieveValid_cons smallPairMask_1_4_22_valid (
                                                  coordinateSquareSieveValid_cons smallPairMask_1_4_23_valid (
                                                    coordinateSquareSieveValid_cons smallPairMask_1_4_24_valid (
                                                      coordinateSquareSieveValid_nil 1 4)))))))))))))))))))))))))

end D1Bound5
end
