-- Prove2me | solution 1 for BitcoinActivation.flags_after_segwit
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:18.445547+00:00
-- url     : https://prove2.me/submissions/5a8dd478-322b-4704-bc46-e1d6b789f1c6

import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- From SegWit activation on, a non-exception block enforces every flag. -/
theorem solution (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .none = ⟨true, true, true, true, true, true, true⟩ := by
  unfold blockScriptFlags exceptionBase baseFlags activeAt deploymentHeight
  have h1 : 363725 ≤ height := by omega
  have h2 : 388381 ≤ height := by omega
  have h3 : 419328 ≤ height := by omega
  simp [h, h1, h2, h3]
