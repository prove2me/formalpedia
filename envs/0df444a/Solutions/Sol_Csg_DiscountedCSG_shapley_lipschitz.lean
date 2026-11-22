-- Prove2me | solution 1 for Csg.DiscountedCSG.shapley_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:45:14.494569+00:00
-- url     : https://prove2.me/submissions/e6d6146a-bce8-403f-9620-9e6022a46329

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Csg_Discounted
import Theorems.Thm_Csg_DiscountedCSG_shapleyGame_A_lipschitz
import Theorems.Thm_Csg_MatrixGame_abs_value_sub_le


set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)
namespace Csg.DiscountedCSG
theorem _root_.solution {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) : |D.shapley v s - D.shapley w s| ≤ D.l * ε := by
  change |(D.shapleyGame s v).value - (D.shapleyGame s w).value| ≤ D.l * ε
  exact MatrixGame.abs_value_sub_le fun a1 a2 => D.shapleyGame_A_lipschitz hε h a1 a2
end Csg.DiscountedCSG
