-- Prove2me | solution 1 for FriedCrossing.TorsionCore.jordan_torsion_eq_neg_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:55:28.344832+00:00
-- url     : https://prove2.me/submissions/f459e79e-1b98-4944-90df-c77c17eff927

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
import Theorems.Thm_FriedCrossing_TorsionCore_jordan_cluster_torsion

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution (sp sz : K) (hsp : sp ≠ 0) (hne : sz ≠ sp) :
    refinedTorsion 1 (sp / (sz - sp)) = -(sz / sp) := by
  have h : sz - sp ≠ 0 := sub_ne_zero.mpr hne
  rw [jordan_cluster_torsion _ (div_ne_zero hsp h)]
  field_simp
  ring
end FriedCrossing.TorsionCore
