-- Prove2me | solution 1 for D1Bound5.smallPairSieve_0_1_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:39:05.672266+00:00
-- url     : https://prove2.me/submissions/943d3e73-1704-404e-a6d8-a1fe1b034bbf

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_cons
import Theorems.Thm_D1Bound5_coordinateSquareSieveValid_nil
import Theorems.Thm_D1Bound5_smallPairMask_0_1_0_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_10_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_11_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_12_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_13_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_14_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_15_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_16_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_17_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_18_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_19_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_1_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_20_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_21_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_22_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_23_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_24_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_2_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_3_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_4_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_5_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_6_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_7_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_8_valid
import Theorems.Thm_D1Bound5_smallPairMask_0_1_9_valid

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0














































































theorem _root_.solution : CoordinateSquareSieveValid 0 1 smallPairSieve_0_1 := by
  exact
    coordinateSquareSieveValid_cons smallPairMask_0_1_0_valid (
      coordinateSquareSieveValid_cons smallPairMask_0_1_1_valid (
        coordinateSquareSieveValid_cons smallPairMask_0_1_2_valid (
          coordinateSquareSieveValid_cons smallPairMask_0_1_3_valid (
            coordinateSquareSieveValid_cons smallPairMask_0_1_4_valid (
              coordinateSquareSieveValid_cons smallPairMask_0_1_5_valid (
                coordinateSquareSieveValid_cons smallPairMask_0_1_6_valid (
                  coordinateSquareSieveValid_cons smallPairMask_0_1_7_valid (
                    coordinateSquareSieveValid_cons smallPairMask_0_1_8_valid (
                      coordinateSquareSieveValid_cons smallPairMask_0_1_9_valid (
                        coordinateSquareSieveValid_cons smallPairMask_0_1_10_valid (
                          coordinateSquareSieveValid_cons smallPairMask_0_1_11_valid (
                            coordinateSquareSieveValid_cons smallPairMask_0_1_12_valid (
                              coordinateSquareSieveValid_cons smallPairMask_0_1_13_valid (
                                coordinateSquareSieveValid_cons smallPairMask_0_1_14_valid (
                                  coordinateSquareSieveValid_cons smallPairMask_0_1_15_valid (
                                    coordinateSquareSieveValid_cons smallPairMask_0_1_16_valid (
                                      coordinateSquareSieveValid_cons smallPairMask_0_1_17_valid (
                                        coordinateSquareSieveValid_cons smallPairMask_0_1_18_valid (
                                          coordinateSquareSieveValid_cons smallPairMask_0_1_19_valid (
                                            coordinateSquareSieveValid_cons smallPairMask_0_1_20_valid (
                                              coordinateSquareSieveValid_cons smallPairMask_0_1_21_valid (
                                                coordinateSquareSieveValid_cons smallPairMask_0_1_22_valid (
                                                  coordinateSquareSieveValid_cons smallPairMask_0_1_23_valid (
                                                    coordinateSquareSieveValid_cons smallPairMask_0_1_24_valid (
                                                      coordinateSquareSieveValid_nil 0 1)))))))))))))))))))))))))

end D1Bound5
end
