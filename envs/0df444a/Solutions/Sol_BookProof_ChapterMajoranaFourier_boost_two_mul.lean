-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.boost_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:40:58.406223+00:00
-- url     : https://prove2.me/submissions/6dec9c21-257e-49cf-b56f-df1c01da23e5

-- Generated from ChapterMajoranaFourier.lean — solution of BookProof.ChapterMajoranaFourier.boost_two_mul
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaFourier



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q) :
    2 * boostC m q * boostS m q = q / Ep m q := by

      unfold boostC boostS Ep; ring_nf; norm_num [ hq.le ] ;
      rw [ ← Real.sqrt_mul ( by positivity ) ] ; ring;
      field_simp;
      rw [ Real.sq_sqrt ( by positivity ), Real.sqrt_div' ] <;> ring <;> norm_num [ hq.le, hm ];
      · rw [ show m ^ 2 * 4 + q ^ 2 * 4 = ( m ^ 2 + q ^ 2 ) * 4 by ring, Real.sqrt_mul (
                                                                   by positivity ) ] ; ring;
        rw [ mul_assoc, mul_inv_cancel₀ ( by positivity ), mul_one ];
      · positivity
