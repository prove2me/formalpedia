-- Prove2me | solution 1 for DeletionCode.RecordCodec.decode_encodeHeader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:00:04.521889+00:00
-- url     : https://prove2.me/submissions/97ee5872-37fb-4c3a-a2d1-2b64e0a391bc

import Definitions.Def_DeletionCode_ConcreteDecoder
import Definitions.Def_DeletionCode_DescriptionCount
import Mathlib.Tactic.FinCases
import Definitions.Def_DeletionCode_RecordCodec

set_option autoImplicit true
open DeletionCode DeletionCode.RecordCodec
open HeaderRecovery ConcreteDecoder DescriptionCount
namespace DeletionCode.RecordCodec
theorem _root_.solution (L : ℕ) (header : Header)
    (hrho0 : 1 ≤ header.rho) (hrhoL : header.rho ≤ L) :
    decodeHeader (encodeHeader L header hrho0 hrhoL) = header := by
  cases header with
  | mk orientation rho bit =>
    cases orientation <;> cases bit <;>
      simp [decodeHeader, encodeHeader, orientationCode, bitCode, Nat.add_mod, Nat.mul_mod]
    all_goals
      dsimp at hrho0 hrhoL
      omega
end DeletionCode.RecordCodec
