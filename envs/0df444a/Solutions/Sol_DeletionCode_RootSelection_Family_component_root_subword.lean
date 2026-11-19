-- Prove2me | solution 1 for DeletionCode.RootSelection.Family.component_root_subword
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:10:33.044349+00:00
-- url     : https://prove2.me/submissions/8431af5b-65c1-4dbb-8f3e-098792df01d4

import Definitions.Def_DeletionCode_WordPaths
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
import Definitions.Def_DeletionCode_RootSelection
import Theorems.Thm_DeletionCode_RootSelection_Family_component_root_windows
import Theorems.Thm_DeletionCode_WordPaths_all_windows_occur_implies_subword


set_option autoImplicit true
open DeletionCode DeletionCode.RootSelection
open Windows
open DeletionCode.RootSelection.Family
namespace DeletionCode.RootSelection.Family
theorem _root_.solution {B : Type*} (F : Family B)
    (x : Letters) (n k L : ℕ) (hx : KUnique x n k) (hk : k < L)
    (hgen : F.Generating x n L) (b : B) :
    ∃ r a, F.Connected L r b ∧
      a + (L + F.extra r false) ≤ n ∧
      Agree x a (F.path r false) 0 (L + F.extra r false) := by
  obtain ⟨r, hr, hwindows⟩ := F.component_root_windows x n L hgen b
  obtain ⟨a, ha, hagree⟩ := WordPaths.all_windows_occur_implies_subword
    x (F.path r false) n k L (F.extra r false) hx hk hwindows
  exact ⟨r, a, hr, ha, hagree⟩
end DeletionCode.RootSelection.Family
