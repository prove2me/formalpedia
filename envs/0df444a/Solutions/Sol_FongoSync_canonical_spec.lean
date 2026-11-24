-- Prove2me | solution 1 for FongoSync.canonical_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:27.93454+00:00
-- url     : https://prove2.me/submissions/325228b1-0401-4bb7-ba06-f3bf7721c61f

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
import Theorems.Thm_FongoSync_isCanonical_nil
import Theorems.Thm_FongoSync_isCanonical_foldl

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution (E : List Edge) (g : Gid) : IsCanonical E g (canonical E g) := by
  have := isCanonical_foldl E [] id isCanonical_nil g
  simpa [canonical] using this
end FongoSync
