-- Prove2me | solution 1 for Comp.coin_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:42:05.6069+00:00
-- url     : https://prove2.me/submissions/f7a315a5-2c6a-4a86-96e3-3825b5dc3a10

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
import Theorems.Thm_Comp_dirac_ne_zero_iff
import Theorems.Thm_Comp_half_add_half_ne_zero

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution (t u s' : Chain) : coin t u s' ≠ 0 ↔ s' = t ∨ s' = u := by
  unfold coin
  rw [half_add_half_ne_zero (dirac_nonneg t s') (dirac_nonneg u s'), dirac_ne_zero_iff,
    dirac_ne_zero_iff]
end Comp
