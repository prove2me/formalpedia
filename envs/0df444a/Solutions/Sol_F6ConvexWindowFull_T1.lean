-- Prove2me | solution 1 for F6ConvexWindowFull.T1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:03:12.6548+00:00
-- url     : https://prove2.me/submissions/5992604d-f917-4781-b325-c8c26b3591cb

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Theorems.Thm_F6ConvexWindow_target1_triples


set_option autoImplicit true
noncomputable section
open F6ConvexWindowFull
open F6ConvexWindow
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindowFull
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (hpos : 0 < Ak (V := V) 3) : 2 * Ak (V := V) 3 + 1 ≤ Fintype.card V :=
  target1_triples hw hci hpos
end F6ConvexWindowFull
