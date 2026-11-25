-- Prove2me | solution 1 for F6ConvexWindow.triplesDescending_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:16:59.014584+00:00
-- url     : https://prove2.me/submissions/608e11d9-66e4-4bef-9978-76c1943f5675

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (F : Finset (Finset V)) :
    (triplesDescending F).toFinset = F := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    by_cases hn : F.Nonempty
    · rw [triplesDescending, dif_pos hn, List.toFinset_cons,
        ih _ (erase_ssubset (lastTriple_mem F hn)), insert_erase (lastTriple_mem F hn)]
    · rw [triplesDescending, dif_neg hn]
      exact (not_nonempty_iff_eq_empty.mp hn).symm
end F6ConvexWindow
