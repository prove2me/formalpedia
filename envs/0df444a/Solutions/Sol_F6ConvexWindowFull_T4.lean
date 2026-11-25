-- Prove2me | solution 1 for F6ConvexWindowFull.T4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:02:20.635385+00:00
-- url     : https://prove2.me/submissions/905f8e64-003c-4325-a584-82b0b46d640f

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Theorems.Thm_F6ConvexWindow_width2_chain_decomposition
import Theorems.Thm_F6ConvexWindow_target4_antichains36_two_chains


set_option autoImplicit true
noncomputable section
open F6ConvexWindowFull
open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindowFull
theorem _root_.solution (hw : WidthLE (V := V) 2) (hci : CI2 (V := V))
    (hn : Fintype.card V ≤ 15) : totalAntichains (V := V) ≤ 36 := by
  obtain ⟨d⟩ := width2_chain_decomposition hw
  exact target4_antichains36_two_chains hw hci hn d
end F6ConvexWindowFull
