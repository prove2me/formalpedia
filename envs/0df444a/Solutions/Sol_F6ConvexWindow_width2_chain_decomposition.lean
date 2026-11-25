-- Prove2me | solution 1 for F6ConvexWindow.width2_chain_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:57:15.687172+00:00
-- url     : https://prove2.me/submissions/84d00622-f206-43b8-854f-a43433acc286

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Theorems.Thm_F6ConvexWindow_width2_antichain_card_le
import Theorems.Thm_F6ConvexWindow_chain_cover_to_decomposition
import Theorems.Thm_DilworthTheorem_dilworth_theorem


set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 2) :
    Nonempty (ChainDecomposition (V := V) 2) := by
  classical
  obtain ⟨C, hC⟩ := DilworthTheorem.dilworth_theorem (univ : Finset V) 2
    (fun A _ hA => width2_antichain_card_le hw A hA)
  exact chain_cover_to_decomposition C hC
end F6ConvexWindow
