-- Prove2me | solution 1 for BitcoinActivation.exception_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:21.124335+00:00
-- url     : https://prove2.me/submissions/7d6455c6-e993-4645-98ff-49053c1ed4ce

import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- An exception never enforces a flag the default would not: exceptions only remove rules. -/
theorem solution (height : Nat) (exc : ScriptException) :
    BitcoinActivation.ScriptFlags.le (BitcoinActivation.blockScriptFlags height exc)
      (BitcoinActivation.blockScriptFlags height .none) := by
  cases exc <;>
  · unfold blockScriptFlags exceptionBase baseFlags noFlags ScriptFlags.le
    simp
