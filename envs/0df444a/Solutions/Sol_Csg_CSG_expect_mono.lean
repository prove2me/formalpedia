-- Prove2me | solution 1 for Csg.CSG.expect_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:34:52.921283+00:00
-- url     : https://prove2.me/submissions/2e790db2-5aac-4a4d-991f-b8b2f53f1489

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution {s : S} {a1 : A1} {a2 : A2} {v w : S → ℝ} (hle : ∀ s', v s' ≤ w s') :
    C.expect s a1 a2 v ≤ C.expect s a1 a2 w := by
  unfold expect
  exact Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hle s') ENNReal.toReal_nonneg
end Csg.CSG
