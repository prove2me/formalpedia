-- Prove2me | solution 1 for D1Bound5.smallPairSieve_0_2_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:40:48.189065+00:00
-- url     : https://prove2.me/submissions/a3111327-0798-4162-8d4b-32d1517d4fb0

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_2_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_cons
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_nil
import Theorems.Thm_D1Bound5_smallPairMask_0_2_0_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_10_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_11_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_12_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_13_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_14_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_15_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_16_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_17_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_18_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_19_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_1_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_20_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_21_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_22_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_23_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_24_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_2_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_3_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_4_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_5_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_6_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_7_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_8_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_2_9_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.solution : CoordinateSquareSieveValid 0 2 smallPairSieve_0_2 := by
  exact
    coordinateSquareSieveValid_cons smallPairMask_0_2_0_valid (
      coordinateSquareSieveValid_cons smallPairMask_0_2_1_valid (
        coordinateSquareSieveValid_cons smallPairMask_0_2_2_valid (
          coordinateSquareSieveValid_cons smallPairMask_0_2_3_valid (
            coordinateSquareSieveValid_cons smallPairMask_0_2_4_valid (
              coordinateSquareSieveValid_cons smallPairMask_0_2_5_valid (
                coordinateSquareSieveValid_cons smallPairMask_0_2_6_valid (
                  coordinateSquareSieveValid_cons smallPairMask_0_2_7_valid (
                    coordinateSquareSieveValid_cons smallPairMask_0_2_8_valid (
                      coordinateSquareSieveValid_cons smallPairMask_0_2_9_valid (
                        coordinateSquareSieveValid_cons smallPairMask_0_2_10_valid (
                          coordinateSquareSieveValid_cons smallPairMask_0_2_11_valid (
                            coordinateSquareSieveValid_cons smallPairMask_0_2_12_valid (
                              coordinateSquareSieveValid_cons smallPairMask_0_2_13_valid (
                                coordinateSquareSieveValid_cons smallPairMask_0_2_14_valid (
                                  coordinateSquareSieveValid_cons smallPairMask_0_2_15_valid (
                                    coordinateSquareSieveValid_cons smallPairMask_0_2_16_valid (
                                      coordinateSquareSieveValid_cons smallPairMask_0_2_17_valid (
                                        coordinateSquareSieveValid_cons smallPairMask_0_2_18_valid (
                                          coordinateSquareSieveValid_cons smallPairMask_0_2_19_valid (
                                            coordinateSquareSieveValid_cons smallPairMask_0_2_20_valid (
                                              coordinateSquareSieveValid_cons smallPairMask_0_2_21_valid (
                                                coordinateSquareSieveValid_cons smallPairMask_0_2_22_valid (
                                                  coordinateSquareSieveValid_cons smallPairMask_0_2_23_valid (
                                                    coordinateSquareSieveValid_cons smallPairMask_0_2_24_valid (
                                                      coordinateSquareSieveValid_nil 0 2)))))))))))))))))))))))))

end D1Bound5
end
