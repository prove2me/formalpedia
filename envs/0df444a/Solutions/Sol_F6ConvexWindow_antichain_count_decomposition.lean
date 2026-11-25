-- Prove2me | solution 1 for F6ConvexWindow.antichain_count_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:03:22.584545+00:00
-- url     : https://prove2.me/submissions/9b72bfc6-0dd0-4559-babd-20b26a8b147d

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_antichains
attribute [local simp] F6ConvexWindow.mem_antichains

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (k : ℕ) (hw : WidthLE (V := V) k) :
    totalAntichains (V := V) = ∑ j ∈ range (k + 1), Ak (V := V) j := by
  classical
  exact card_eq_sum_card_fiberwise (f := Finset.card) (s := antichains)
    (t := range (k + 1)) (fun s hs => mem_range.mpr (Nat.lt_succ_of_le (hw s (mem_antichains.mp hs))))
end F6ConvexWindow
