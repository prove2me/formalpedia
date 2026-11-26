-- Prove2me | solution 1 for FirstPassageLinearTransport.maximalBarrierHeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:17.817454+00:00
-- url     : https://prove2.me/submissions/f02687a7-d523-49c9-a4e8-5dc823535bc0

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_pos

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {t : ℝ} {M : ℕ} (ht : 0 ≤ t) :
    0 ≤ maximalBarrierHeight t M := by
  unfold maximalBarrierHeight
  exact div_nonneg (mul_nonneg ht (Nat.cast_nonneg M))
    (mul_nonneg (by norm_num) logTwoThree_pos.le)
end FirstPassageLinearTransport
