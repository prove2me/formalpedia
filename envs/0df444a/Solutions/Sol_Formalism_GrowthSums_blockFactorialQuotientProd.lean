-- Prove2me | solution 1 for Formalism.GrowthSums.blockFactorialQuotientProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:20.71611+00:00
-- url     : https://prove2.me/submissions/48197389-6657-4f2c-91e3-f60a49ab0beb

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Coarse
import Theorems.Thm_Formalism_GrowthSums_coarseUnit_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
namespace Formalism.GrowthSums
theorem _root_.solution : CoarseUnitProd := by
  intro P n hP
  induction n with
  | zero => simp [coarseUnit]
  | succ n ih => rw [coarseUnit_succ P n hP, ih, Finset.prod_range_succ]
end Formalism.GrowthSums
