-- Prove2me | solution 1 for D1Bound5.smallPairSieve_1_6_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:40:50.941814+00:00
-- url     : https://prove2.me/submissions/a96daa3e-ac31-440a-aff3-bd6916f99201

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_6_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_cons
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_nil
import Theorems.Thm_D1Bound5_smallPairMask_1_6_0_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_10_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_11_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_12_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_13_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_14_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_15_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_16_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_17_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_18_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_19_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_1_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_20_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_21_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_22_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_23_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_24_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_2_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_3_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_4_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_5_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_6_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_7_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_8_valid
import Theorems.Thm_D1Bound5_smallPairMask_1_6_9_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.solution : CoordinateSquareSieveValid 1 6 smallPairSieve_1_6 := by
  exact
    coordinateSquareSieveValid_cons smallPairMask_1_6_0_valid (
      coordinateSquareSieveValid_cons smallPairMask_1_6_1_valid (
        coordinateSquareSieveValid_cons smallPairMask_1_6_2_valid (
          coordinateSquareSieveValid_cons smallPairMask_1_6_3_valid (
            coordinateSquareSieveValid_cons smallPairMask_1_6_4_valid (
              coordinateSquareSieveValid_cons smallPairMask_1_6_5_valid (
                coordinateSquareSieveValid_cons smallPairMask_1_6_6_valid (
                  coordinateSquareSieveValid_cons smallPairMask_1_6_7_valid (
                    coordinateSquareSieveValid_cons smallPairMask_1_6_8_valid (
                      coordinateSquareSieveValid_cons smallPairMask_1_6_9_valid (
                        coordinateSquareSieveValid_cons smallPairMask_1_6_10_valid (
                          coordinateSquareSieveValid_cons smallPairMask_1_6_11_valid (
                            coordinateSquareSieveValid_cons smallPairMask_1_6_12_valid (
                              coordinateSquareSieveValid_cons smallPairMask_1_6_13_valid (
                                coordinateSquareSieveValid_cons smallPairMask_1_6_14_valid (
                                  coordinateSquareSieveValid_cons smallPairMask_1_6_15_valid (
                                    coordinateSquareSieveValid_cons smallPairMask_1_6_16_valid (
                                      coordinateSquareSieveValid_cons smallPairMask_1_6_17_valid (
                                        coordinateSquareSieveValid_cons smallPairMask_1_6_18_valid (
                                          coordinateSquareSieveValid_cons smallPairMask_1_6_19_valid (
                                            coordinateSquareSieveValid_cons smallPairMask_1_6_20_valid (
                                              coordinateSquareSieveValid_cons smallPairMask_1_6_21_valid (
                                                coordinateSquareSieveValid_cons smallPairMask_1_6_22_valid (
                                                  coordinateSquareSieveValid_cons smallPairMask_1_6_23_valid (
                                                    coordinateSquareSieveValid_cons smallPairMask_1_6_24_valid (
                                                      coordinateSquareSieveValid_nil 1 6)))))))))))))))))))))))))

end D1Bound5
end
