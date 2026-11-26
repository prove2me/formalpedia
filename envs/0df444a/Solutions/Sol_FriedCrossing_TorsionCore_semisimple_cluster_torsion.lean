-- Prove2me | solution 1 for FriedCrossing.TorsionCore.semisimple_cluster_torsion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:59.293945+00:00
-- url     : https://prove2.me/submissions/5795a218-5ffe-4c66-9cd8-3007e903730e

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
import Theorems.Thm_FriedCrossing_TorsionCore_refinedTorsion_eq

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution (l : K) (hl : l ≠ 0) : refinedTorsion 0 l = -1 := by
  rw [refinedTorsion_eq 0 l hl, add_zero, neg_div, div_self hl]
end FriedCrossing.TorsionCore
