-- Prove2me | solution 1 for DeletionCode.OptimalRedundancy.singleton_corrects
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:12:23.801945+00:00
-- url     : https://prove2.me/submissions/408d1265-9cfc-42cb-95b8-279011173ccf

import Definitions.Def_DeletionCode_CodeExistence
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_DeletionCode_OptimalRedundancy
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans


set_option autoImplicit true
open DeletionCode DeletionCode.OptimalRedundancy
open HeaderRecovery Filter
namespace DeletionCode.OptimalRedundancy
theorem _root_.solution (t n : ℕ) (x : Bits n) :
    CodeSelection.Corrects t ({x} : Finset (Bits n)) := by
  classical
  intro a ha b hb hne
  have ha' : a = x := Finset.mem_singleton.mp ha
  have hb' : b = x := Finset.mem_singleton.mp hb
  exact False.elim (hne (ha'.trans hb'.symm))
end DeletionCode.OptimalRedundancy
