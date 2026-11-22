-- Prove2me | solution 1 for Csg.CSG.expect_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:35:12.466487+00:00
-- url     : https://prove2.me/submissions/1b0fafbe-e793-49f9-97b5-68d357659d83

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution {s : S} {a1 : A1} {a2 : A2} {v : S → ℝ} (hv : ∀ s', 0 ≤ v s') :
    0 ≤ C.expect s a1 a2 v := by
  unfold expect
  exact Finset.sum_nonneg fun s' _ => mul_nonneg ENNReal.toReal_nonneg (hv s')
end Csg.CSG
