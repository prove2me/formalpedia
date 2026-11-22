-- Prove2me | solution 1 for Csg.DiscountedCSG.shapleyGame_A_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:42:00.43601+00:00
-- url     : https://prove2.me/submissions/8776518b-b9bd-4448-bc33-229c325957df

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Csg_Discounted
import Theorems.Thm_Csg_CSG_expect_lipschitz


set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) (a1 : A1) (a2 : A2) :
    |(D.shapleyGame s v).A a1 a2 - (D.shapleyGame s w).A a1 a2| ≤ D.l * ε := by
  have heq : (D.shapleyGame s v).A a1 a2 - (D.shapleyGame s w).A a1 a2
      = D.l * (D.toCSG.expect s a1 a2 v - D.toCSG.expect s a1 a2 w) := by
    change (D.toCSG.r s a1 a2 + D.l * D.toCSG.expect s a1 a2 v)
        - (D.toCSG.r s a1 a2 + D.l * D.toCSG.expect s a1 a2 w) = _
    ring
  rw [heq, abs_mul, abs_of_nonneg D.l_nonneg]
  exact mul_le_mul_of_nonneg_left (D.toCSG.expect_lipschitz hε h) D.l_nonneg
end Csg.DiscountedCSG
