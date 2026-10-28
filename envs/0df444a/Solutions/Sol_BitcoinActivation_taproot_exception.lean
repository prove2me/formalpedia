-- Prove2me | solution 1 for BitcoinActivation.taproot_exception
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:20.505273+00:00
-- url     : https://prove2.me/submissions/dc014c89-bcbb-4b88-89a7-a046ef1d3458

import Definitions.Def_BitcoinActivation

open BitcoinActivation

/-- The Taproot exception block (height 692261, after SegWit) enforces every flag except Taproot. -/
theorem solution (height : Nat) (h : 481824 ≤ height) :
    BitcoinActivation.blockScriptFlags height .taprootBlock = ⟨true, true, false, true, true, true, true⟩ := by
  unfold blockScriptFlags exceptionBase activeAt deploymentHeight
  have h1 : 363725 ≤ height := by omega
  have h2 : 388381 ≤ height := by omega
  have h3 : 419328 ≤ height := by omega
  simp [h, h1, h2, h3]
