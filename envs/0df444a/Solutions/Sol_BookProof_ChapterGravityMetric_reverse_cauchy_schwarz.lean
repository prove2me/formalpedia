-- Prove2me | solution 1 for BookProof.ChapterGravityMetric.reverse_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:52:34.629982+00:00
-- url     : https://prove2.me/submissions/29ece24d-d994-46bf-aaee-c8253151b435

-- Generated from ChapterGravityMetric.lean — solution of BookProof.ChapterGravityMetric.reverse_cauchy_schwarz
import Mathlib
import Definitions.Def_ChapterGravityMetric
open BookProof.ChapterGravityMetric




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v x : Fin 4 → ℝ) (hv : minkSq v = -1) :
    0 ≤ (∑ a, x a * lower v a) ^ 2 + minkSq x := by

      unfold minkSq at *; norm_num [ Fin.sum_univ_four, lower ] at *;
      unfold metric at * ; norm_num [ Fin.sum_univ_four, Matrix.mulVec ] at *;
      norm_num [ Fin.ext_iff ] at *;
      by_cases h : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 0;
      · norm_num [ show v 1 = 0 by nlinarith only [ h ], show v 2 = 0
                                   by nlinarith only [ h ], show v 3 = 0
                                       by nlinarith only [ h ] ] at *;
        nlinarith [ sq_nonneg ( x 1 ), sq_nonneg ( x 2 ), sq_nonneg ( x 3 ) ];
      · -- Let's simplify the expression by setting $a = x_1 v_1 + x_2 v_2 + x_3 v_3$ and $s = v_1^2
        -- + v_2^2 + v_3^2$.
        set a := x 1 * v 1 + x 2 * v 2 + x 3 * v 3
        set s := v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2
        have h_s_pos : 0 < s := by
          exact lt_of_le_of_ne ( by positivity ) ( Ne.symm h );
        -- Substitute $a$ and $s$ into the inequality.
        have h_sub : s * ((-(x 0 * v 0) + a) ^ 2 + (-(x 0 * x 0) + x 1 * x 1 + x 2 * x 2 + x 3 * x
            3)) = (a * v 0 - x 0 * s) ^ 2 + (s * (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) - a ^ 2) := by
          grind;
        -- By the Lagrange identity, we know that $s * (x_1^2 + x_2^2 + x_3^2) - a^2 \geq 0$.
        have h_lagrange : s * (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) - a ^ 2 ≥ 0 := by
          nlinarith only [ sq_nonneg ( x 1 * v 2 - x 2 * v 1 ), sq_nonneg ( x 1 * v 3 - x 3 * v 1 ),
              sq_nonneg ( x 2 * v 3 - x 3 * v 2 ) ];
        nlinarith only [ h_sub, h_lagrange, h_s_pos ]
