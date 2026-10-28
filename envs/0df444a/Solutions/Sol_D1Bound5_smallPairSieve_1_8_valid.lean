-- Prove2me | solution 1 for D1Bound5.smallPairSieve_1_8_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:40:46.64633+00:00
-- url     : https://prove2.me/submissions/3d8a64cf-d775-46c1-9538-63765ed7ac30

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_8_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_cons
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_nil
import Theorems.Thm_D1Bound5_smallPairMask_1_8_0_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_10_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_11_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_12_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_13_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_14_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_15_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_16_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_17_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_18_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_19_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_1_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_20_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_21_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_22_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_23_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_24_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_2_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_3_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_4_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_5_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_6_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_7_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_8_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_8_9_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.solution : CoordinateSquareSieveValid 1 8 smallPairSieve_1_8 := by
  exact
    coordinateSquareSieveValid_cons smallPairMask_1_8_0_valid (
      coordinateSquareSieveValid_cons smallPairMask_1_8_1_valid (
        coordinateSquareSieveValid_cons smallPairMask_1_8_2_valid (
          coordinateSquareSieveValid_cons smallPairMask_1_8_3_valid (
            coordinateSquareSieveValid_cons smallPairMask_1_8_4_valid (
              coordinateSquareSieveValid_cons smallPairMask_1_8_5_valid (
                coordinateSquareSieveValid_cons smallPairMask_1_8_6_valid (
                  coordinateSquareSieveValid_cons smallPairMask_1_8_7_valid (
                    coordinateSquareSieveValid_cons smallPairMask_1_8_8_valid (
                      coordinateSquareSieveValid_cons smallPairMask_1_8_9_valid (
                        coordinateSquareSieveValid_cons smallPairMask_1_8_10_valid (
                          coordinateSquareSieveValid_cons smallPairMask_1_8_11_valid (
                            coordinateSquareSieveValid_cons smallPairMask_1_8_12_valid (
                              coordinateSquareSieveValid_cons smallPairMask_1_8_13_valid (
                                coordinateSquareSieveValid_cons smallPairMask_1_8_14_valid (
                                  coordinateSquareSieveValid_cons smallPairMask_1_8_15_valid (
                                    coordinateSquareSieveValid_cons smallPairMask_1_8_16_valid (
                                      coordinateSquareSieveValid_cons smallPairMask_1_8_17_valid (
                                        coordinateSquareSieveValid_cons smallPairMask_1_8_18_valid (
                                          coordinateSquareSieveValid_cons smallPairMask_1_8_19_valid (
                                            coordinateSquareSieveValid_cons smallPairMask_1_8_20_valid (
                                              coordinateSquareSieveValid_cons smallPairMask_1_8_21_valid (
                                                coordinateSquareSieveValid_cons smallPairMask_1_8_22_valid (
                                                  coordinateSquareSieveValid_cons smallPairMask_1_8_23_valid (
                                                    coordinateSquareSieveValid_cons smallPairMask_1_8_24_valid (
                                                      coordinateSquareSieveValid_nil 1 8)))))))))))))))))))))))))

end D1Bound5
end
