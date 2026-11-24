-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.norm_lt_one_of_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:37.473434+00:00
-- url     : https://prove2.me/submissions/afc3396b-2ca2-4bfe-8fe4-f6075af0461a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset
namespace Formalism.MainNotions.WeightedLatticeSum
theorem _root_.solution (z w : ℂ) (h1 : ⌊2 * z.re⌋ = ⌊2 * w.re⌋) (h2 : ⌊2 * z.im⌋ = ⌊2 * w.im⌋) :
    ‖z - w‖ < 1 := by
  have a1 := Int.floor_le (2 * z.re)
  have a2 := Int.lt_floor_add_one (2 * z.re)
  have b1 := Int.floor_le (2 * w.re)
  have b2 := Int.lt_floor_add_one (2 * w.re)
  have c1 := Int.floor_le (2 * z.im)
  have c2 := Int.lt_floor_add_one (2 * z.im)
  have d1 := Int.floor_le (2 * w.im)
  have d2 := Int.lt_floor_add_one (2 * w.im)
  rw [h1] at a1 a2
  rw [h2] at c1 c2
  have kre : 0 < (1 - (2 * z.re - 2 * w.re)) * (1 + (2 * z.re - 2 * w.re)) :=
    mul_pos (by linarith) (by linarith)
  have im_algebraMap_add_mul : 0 < (1 - (2 * z.im - 2 * w.im)) * (1 + (2 * z.im - 2 * w.im)) :=
    mul_pos (by linarith) (by linarith)
  have hn : ‖z - w‖ ^ 2 < 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith
  nlinarith [norm_nonneg (z - w)]
end Formalism.MainNotions.WeightedLatticeSum
