-- Prove2me | solution 1 for F6ConvexWindowFull.T2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:00:59.690998+00:00
-- url     : https://prove2.me/submissions/15a041a7-a1bc-477e-8c5a-565723f446ef

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Theorems.Thm_F6ConvexWindow_w3_chain_decomposition
import Theorems.Thm_F6ConvexWindow_target2_pairs_three_chains


set_option autoImplicit true
noncomputable section
open F6ConvexWindowFull
open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindowFull
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) : Ak (V := V) 2 + 3 ≤ 2 * Fintype.card V := by
  obtain ⟨d⟩ := w3_chain_decomposition hw
  exact target2_pairs_three_chains hw hci hpos d
end F6ConvexWindowFull
