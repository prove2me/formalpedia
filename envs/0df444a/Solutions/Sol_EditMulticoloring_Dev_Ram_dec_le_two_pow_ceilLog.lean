-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.dec_le_two_pow_ceilLog
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:28.004345+00:00
-- url     : https://prove2.me/submissions/76b6b100-8c2d-442d-bfb4-d83f6c8b6657

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

theorem dec_le_two_pow_ceilLog_oai (X : ℕ) : X ≤ 2 ^ ceilLog 2 X := by
  show X ≤ 2 ^ (if X ≤ 2 ^ Nat.log 2 X then Nat.log 2 X else Nat.log 2 X + 1)
  split_ifs with h
  · exact h
  · exact (Nat.lt_pow_succ_log_self (by norm_num) X).le

/-! ## The program -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.dec_le_two_pow_ceilLog_oai := @EditMulticoloring.Dev.Ram.dec_le_two_pow_ceilLog_oai
