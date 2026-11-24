-- Prove2me | solution 1 for FongoSync.Laws.canonical_is_smallest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:42.771389+00:00
-- url     : https://prove2.me/submissions/574e6cf6-e5c8-4595-8ac4-5e6ef7e41faf

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_canonical_spec


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (E : List Edge) (g : Gid) :
    Connected E g (canonical E g) ∧ ∀ h, Connected E g h → canonical E g ≤ h :=
  canonical_spec E g
end FongoSync.Laws
