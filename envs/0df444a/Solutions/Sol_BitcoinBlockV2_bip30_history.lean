-- Prove2me | solution 1 for BitcoinBlockV2.bip30_history
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:12:19.30689+00:00
-- url     : https://prove2.me/submissions/0513671c-4a8e-4e9d-9075-2fb8af72427f

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader

open BitcoinBlockV2 in
theorem solution (S : ChainState) (height : Nat) (hash : BitcoinSer.Bytes) :
    BitcoinBlockV2.bip30Checked S height hash = false ↔
      height < BIP34_IMPLIES_BIP30_LIMIT ∧
      (BitcoinBlockV2.isBIP30Repeat height hash = true ∨
        ∃ h, S.headers[BitcoinHeader.BIP34Height]? = some h ∧ BitcoinSer.headerHash h = BitcoinBlockV2.bip34Hash) := by
  unfold bip30Checked
  cases hh : S.headers[BitcoinHeader.BIP34Height]? with
  | none => simp [and_comm]
  | some x =>
    simp
    cases isBIP30Repeat height hash <;> simp [and_comm]
