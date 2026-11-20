-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.dec_one_le_r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:55.713059+00:00
-- url     : https://prove2.me/submissions/aea491bc-e300-46a1-a5dc-2eaddac5a11e

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine

section
-- module Solutions.EditMulticoloring.RamDecode4
/-!
# The decoder, part 4: the program `decProg` and its specification (q379, Part D)

The short-table routine is taken from `RamEncodeS4` (namespace `EncS`, a verbatim copy of
`RamShort*`), because `RamShort` and `RamColor` cannot be imported together (name clashes
`value_lt`, `visBound`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The split of a short-code index -/

/-! ## Monotone bounds -/

theorem dec_one_le_r_oai (q t n : ℕ) (hq : 1 ≤ q) : 1 ≤ (parameters q t n).r := by
  show 1 ≤ radiusBound q (2 * t) n
  unfold radiusBound
  have : 1 ≤ (2 * q * (n + 2 * t + 1)) ^ (2 * t) := Nat.one_le_pow _ _ (by positivity)
  nlinarith

/-! ## The program -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.dec_one_le_r_oai := @EditMulticoloring.Dev.Ram.dec_one_le_r_oai
