-- Prove2me | solution 1 for DeletionCode.RootSelection.Family.supplier_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:59:13.558592+00:00
-- url     : https://prove2.me/submissions/aed15d99-e4aa-4e5c-a21c-de827c08093c

import Definitions.Def_DeletionCode_WordPaths
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
import Definitions.Def_DeletionCode_RootSelection

set_option autoImplicit true
open DeletionCode DeletionCode.RootSelection
open Windows
open DeletionCode.RootSelection.Family
namespace DeletionCode.RootSelection.Family
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (b a : B) (side : Bool) (i j : ℕ)
    (hi : i ≤ F.extra b false) (hj : j ≤ F.extra a side)
    (hgram : Agree (F.path b false) i (F.path a side) j L) :
    F.Adjacent L b a := by
  refine ⟨false, side, i, j, by omega, by omega, by omega, by omega, ?_⟩
  intro q hq
  exact hgram q (by omega)
end DeletionCode.RootSelection.Family
