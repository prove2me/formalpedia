-- Prove2me | solution 1 for D1Bound5.smallPairSieve_1_3_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:39:02.414082+00:00
-- url     : https://prove2.me/submissions/fc5fabcd-0d71-4ec1-b28d-b1461c96eafd

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_3_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_cons
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_nil
import Theorems.Thm_D1Bound5_smallPairMask_1_3_0_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_10_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_11_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_12_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_13_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_14_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_15_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_16_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_17_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_18_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_19_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_1_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_20_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_21_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_22_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_23_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_24_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_2_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_3_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_4_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_5_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_6_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_7_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_8_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_3_9_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.solution : CoordinateSquareSieveValid 1 3 smallPairSieve_1_3 := by
  exact
    coordinateSquareSieveValid_cons smallPairMask_1_3_0_valid (
      coordinateSquareSieveValid_cons smallPairMask_1_3_1_valid (
        coordinateSquareSieveValid_cons smallPairMask_1_3_2_valid (
          coordinateSquareSieveValid_cons smallPairMask_1_3_3_valid (
            coordinateSquareSieveValid_cons smallPairMask_1_3_4_valid (
              coordinateSquareSieveValid_cons smallPairMask_1_3_5_valid (
                coordinateSquareSieveValid_cons smallPairMask_1_3_6_valid (
                  coordinateSquareSieveValid_cons smallPairMask_1_3_7_valid (
                    coordinateSquareSieveValid_cons smallPairMask_1_3_8_valid (
                      coordinateSquareSieveValid_cons smallPairMask_1_3_9_valid (
                        coordinateSquareSieveValid_cons smallPairMask_1_3_10_valid (
                          coordinateSquareSieveValid_cons smallPairMask_1_3_11_valid (
                            coordinateSquareSieveValid_cons smallPairMask_1_3_12_valid (
                              coordinateSquareSieveValid_cons smallPairMask_1_3_13_valid (
                                coordinateSquareSieveValid_cons smallPairMask_1_3_14_valid (
                                  coordinateSquareSieveValid_cons smallPairMask_1_3_15_valid (
                                    coordinateSquareSieveValid_cons smallPairMask_1_3_16_valid (
                                      coordinateSquareSieveValid_cons smallPairMask_1_3_17_valid (
                                        coordinateSquareSieveValid_cons smallPairMask_1_3_18_valid (
                                          coordinateSquareSieveValid_cons smallPairMask_1_3_19_valid (
                                            coordinateSquareSieveValid_cons smallPairMask_1_3_20_valid (
                                              coordinateSquareSieveValid_cons smallPairMask_1_3_21_valid (
                                                coordinateSquareSieveValid_cons smallPairMask_1_3_22_valid (
                                                  coordinateSquareSieveValid_cons smallPairMask_1_3_23_valid (
                                                    coordinateSquareSieveValid_cons smallPairMask_1_3_24_valid (
                                                      coordinateSquareSieveValid_nil 1 3)))))))))))))))))))))))))

end D1Bound5
end
