-- Prove2me | solution 1 for FongoSync.isCanonical_foldl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:04.389358+00:00
-- url     : https://prove2.me/submissions/1fd3e1ea-a8a3-416d-a4ff-9821af3c83ea

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
import Theorems.Thm_FongoSync_Connected_nil
import Theorems.Thm_FongoSync_isCanonical_union

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution (E P : List Edge) (L : Gid → Gid) (inv : ∀ g, IsCanonical P g (L g)) :
    ∀ g, IsCanonical (P ++ E) g (E.foldl union L g) := by
  induction E generalizing P L with
  | nil => simpa using inv
  | cons e E ih =>
    simp only [List.foldl]
    have := ih (P ++ [e]) (union L e) (isCanonical_union inv e)
    simpa using this
end FongoSync
