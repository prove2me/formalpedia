-- Prove2me | solution 1 for F6ConvexWindow.totalAntichains_le_48
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:07:30.072978+00:00
-- url     : https://prove2.me/submissions/1cb24c13-5472-44a8-a1be-fd557ded6481

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_width2_of_A3_zero
import Theorems.Thm_F6ConvexWindow_totalAntichains_le_46_of_six_triples
import Theorems.Thm_F6ConvexWindowFull_T2
import Theorems.Thm_F6ConvexWindowFull_T3
import Theorems.Thm_F6ConvexWindowFull_T4
import Theorems.Thm_F6ConvexWindow_antichain_count_width3


set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hn : Fintype.card V ≤ 15) : totalAntichains (V := V) ≤ 48 := by
  by_cases hz : Ak (V := V) 3 = 0
  · exact (F6ConvexWindowFull.T4 (width2_of_A3_zero hw hz) hci hn).trans (by omega)
  · have hpos : 0 < Ak (V := V) 3 := Nat.pos_of_ne_zero hz
    by_cases hn14 : Fintype.card V ≤ 14
    · exact (F6ConvexWindowFull.T3 hw hci hpos hn14).trans (by omega)
    · have hn15 : Fintype.card V = 15 := by omega
      by_cases ht : 6 ≤ Ak (V := V) 3
      · exact (totalAntichains_le_46_of_six_triples hw hci hn15 ht).trans (by omega)
      · have hpairs := F6ConvexWindowFull.T2 hw hci hpos
        have hcount := antichain_count_width3 hw
        omega
end F6ConvexWindow
