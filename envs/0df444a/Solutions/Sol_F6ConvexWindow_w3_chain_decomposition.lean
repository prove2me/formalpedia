-- Prove2me | solution 1 for F6ConvexWindow.w3_chain_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:57:13.014342+00:00
-- url     : https://prove2.me/submissions/00f31331-84da-42e3-bce3-8ff4a3286da1

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Theorems.Thm_F6ConvexWindow_w3_antichain_card_le
import Theorems.Thm_F6ConvexWindow_chain_cover_to_decomposition
import Theorems.Thm_DilworthTheorem_dilworth_theorem


set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) :
    Nonempty (ChainDecomposition (V := V) 3) := by
  classical
  obtain ⟨C, hC⟩ := DilworthTheorem.dilworth_theorem (univ : Finset V) 3
    (fun A _ hA => w3_antichain_card_le hw A hA)
  exact chain_cover_to_decomposition C hC
end F6ConvexWindow
