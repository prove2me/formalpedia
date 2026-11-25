-- Prove2me | solution 1 for F6ConvexWindow.target3_antichains46_three_chains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:05:14.598333+00:00
-- url     : https://prove2.me/submissions/19a2af63-94ab-44dd-8d74-d3c118303927

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_target1_triples
import Theorems.Thm_F6ConvexWindow_antichain_count_width3
import Theorems.Thm_F6ConvexWindow_target2_pairs_three_chains

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) (hn : Fintype.card V ≤ 14)
    (d : ChainDecomposition (V := V) 3) : totalAntichains (V := V) ≤ 46 := by
  have h3 := target1_triples hw hci hpos
  have h2 := target2_pairs_three_chains hw hci hpos d
  have he := antichain_count_width3 hw
  omega
end F6ConvexWindow
