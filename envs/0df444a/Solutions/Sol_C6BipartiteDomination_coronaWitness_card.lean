-- Prove2me | solution 1 for C6BipartiteDomination.coronaWitness_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:42:59.316975+00:00
-- url     : https://prove2.me/submissions/467d1408-dd0c-4dde-bd6d-dca82bd1870a

import Definitions.Def_C6BipartiteDomination_Basic
import Mathlib.Tactic.FinCases
import Definitions.Def_C6BipartiteDomination_Corona

set_option autoImplicit true
open C6BipartiteDomination
namespace C6BipartiteDomination
theorem _root_.solution : coronaWitness.card = 8 := by
  decide
end C6BipartiteDomination
