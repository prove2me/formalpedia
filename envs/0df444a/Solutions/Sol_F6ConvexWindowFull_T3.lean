-- Prove2me | solution 1 for F6ConvexWindowFull.T3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:01:02.348139+00:00
-- url     : https://prove2.me/submissions/43e6695e-9a38-49e6-9782-9d2a3bd6d936

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Theorems.Thm_F6ConvexWindow_w3_chain_decomposition
import Theorems.Thm_F6ConvexWindow_target3_antichains46_three_chains


set_option autoImplicit true
noncomputable section
open F6ConvexWindowFull
open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindowFull
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) (hn : Fintype.card V ≤ 14) :
    totalAntichains (V := V) ≤ 46 := by
  obtain ⟨d⟩ := w3_chain_decomposition hw
  exact target3_antichains46_three_chains hw hci hpos hn d
end F6ConvexWindowFull
