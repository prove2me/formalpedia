-- Prove2me | solution 1 for F6ConvexWindow.antichain_iff_dilworth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:08:56.722946+00:00
-- url     : https://prove2.me/submissions/2f6a4169-7351-41d0-b54b-322f2f617c4e

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Theorems.Thm_F6ConvexWindow_antichain_inc


set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (A : Finset V) :
    Antichain A ↔ DilworthTheorem.IsAntichain (A : Set V) := by
  constructor
  · intro h x y hx hy hne
    exact antichain_inc h hx hy hne
  · intro h x hx y hy hxy
    by_contra hne
    exact (h x y hx hy hne).1 hxy
end F6ConvexWindow
