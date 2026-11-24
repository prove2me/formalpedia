-- Prove2me | solution 1 for FongoSync.mem_entriesAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:00:22.98885+00:00
-- url     : https://prove2.me/submissions/37a75da6-e19b-4695-b2fc-039868db2e8a

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
omit [Ord V]
namespace FongoSync
theorem _root_.solution {cs : List (Change V)} {k : Key} {e : Entry V} :
    e ∈ entriesAt cs k ↔ ∃ c ∈ cs, c.key = k ∧ c.entry = e := by
  simp [entriesAt, and_assoc]
end FongoSync
