-- Prove2me | solution 1 for BitcoinBlockV2.connectBlock_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:13:04.010373+00:00
-- url     : https://prove2.me/submissions/d6c4bc07-8ff6-4430-90df-b21f818cac2a

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

open BitcoinBlockV2 in
theorem S190BLK_loop_utxo (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat)
    (txs : List BitcoinSer.Tx) (st st' : LoopState) (h : connectLoop f H mtp ltf st txs = some st') :
    st'.utxo = applyTxs H st.utxo txs := by
  induction txs generalizing st with
  | nil => simp [connectLoop] at h; subst h; rfl
  | cons tx rest ih =>
    unfold connectLoop at h
    simp only at h
    split at h
    · cases h
    · rename_i fees undo _
      split at h
      · cases h
      · split at h
        · cases h
        · exact ih _ h

open BitcoinBlockV2 in
theorem S190BLK_cb_apply (S : ChainState) (b : BitcoinSer.Block) (u : Ledger) (undo : BlockUndo)
    (h : connectBlock S b = some (u, undo)) : u = (applySpec S b).utxo := by
  unfold connectBlock at h
  unfold applySpec
  by_cases hg : BitcoinSer.headerHash b.header = BitcoinSer.genesisHash
  · simp only [hg, if_true] at h ⊢
    cases h; rfl
  · simp only [hg, if_false] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i st hl
        split at h
        · cases h
        · cases h
          exact S190BLK_loop_utxo _ _ _ _ _ _ _ hl

open BitcoinBlockV2 in
theorem solution (S : ChainState) (b : BitcoinSer.Block) (u : Ledger) (undo : BlockUndo)
    (h : BitcoinBlockV2.connectBlock S b = some (u, undo)) : u = (BitcoinBlockV2.applySpec S b).utxo :=
  S190BLK_cb_apply S b u undo h
