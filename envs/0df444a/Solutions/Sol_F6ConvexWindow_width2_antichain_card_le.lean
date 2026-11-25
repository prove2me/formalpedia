-- Prove2me | solution 1 for F6ConvexWindow.width2_antichain_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:41:57.640667+00:00
-- url     : https://prove2.me/submissions/3028647d-5764-4bf6-8245-07af433426ae

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Theorems.Thm_F6ConvexWindow_antichain_iff_dilworth

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 2) (A : Finset V)
    (hA : DilworthTheorem.IsAntichain (A : Set V)) : A.card ≤ 2 :=
  hw A ((antichain_iff_dilworth A).mpr hA)
end F6ConvexWindow
