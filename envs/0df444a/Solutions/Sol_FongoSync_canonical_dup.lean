-- Prove2me | solution 1 for FongoSync.canonical_dup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:31.081205+00:00
-- url     : https://prove2.me/submissions/c5f1038a-8ff8-49f3-8f78-518b5130b54f

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
import Theorems.Thm_FongoSync_canonical_eq_of_mem_iff

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution (E : List Edge) : canonical (E ++ E) = canonical E :=
  canonical_eq_of_mem_iff _ _ (by simp)
end FongoSync
