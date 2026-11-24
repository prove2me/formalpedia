-- Prove2me | solution 1 for FongoSync.canonical_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:04:53.06451+00:00
-- url     : https://prove2.me/submissions/abad5b72-74ce-45e1-8c41-65fc9840010d

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
import Theorems.Thm_FongoSync_label_eq_of_connected
import Theorems.Thm_FongoSync_connected_of_label_eq
import Theorems.Thm_FongoSync_canonical_spec

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution (E : List Edge) (a b : Gid) :
    canonical E a = canonical E b ↔ Connected E a b :=
  ⟨connected_of_label_eq (canonical_spec E), label_eq_of_connected (canonical_spec E)⟩
end FongoSync
