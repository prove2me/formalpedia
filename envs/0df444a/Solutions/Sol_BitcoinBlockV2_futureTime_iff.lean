-- Prove2me | solution 1 for BitcoinBlockV2.futureTime_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:12:45.641995+00:00
-- url     : https://prove2.me/submissions/856e9995-dd89-477b-a3a9-e911adfa14b4

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer
open BitcoinBlockV2 in
theorem S190BLK_acc_ne_ft (S : ChainState) (b : BitcoinSer.Block) :
    (if !checkBlock b then Outcome.invalid
    else if !contextualCheckBlock S b then .invalid
    else match connectBlock S b with
      | none => .invalid
      | some (u, undo) => .accept ⟨S.headers ++ [b.header], u⟩ undo) ≠ .futureTime := by
  split
  · simp
  · split
    · simp
    · split <;> simp

open BitcoinBlockV2 in
theorem S190BLK_ft_iff (S : ChainState) (b : BitcoinSer.Block) (now : Int) :
    validate S b now = .futureTime ↔ acceptHeader S b.header now = .futureTime := by
  unfold validate
  split
  · rename_i h
    rw [h]
    constructor
    · intro h2; exact absurd h2 (S190BLK_acc_ne_ft S b)
    · intro h2; cases h2
  all_goals rfl

open BitcoinBlockV2 in
theorem solution (S : ChainState) (b : BitcoinSer.Block) (now : Int) :
    BitcoinBlockV2.validate S b now = .futureTime ↔
      BitcoinBlockV2.checkHeaderPow b.header = true ∧ b.header.prevBlock = S.tipHash ∧
      BitVec.ofNat 32 b.header.bits = S.requiredBits ∧ S.mtp < (b.header.time : Int) ∧
      now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) := by
  rw [S190BLK_ft_iff]
  unfold acceptHeader
  by_cases h1 : checkHeaderPow b.header = true <;> simp only [h1] <;> simp
  by_cases h2 : b.header.prevBlock = S.tipHash <;> simp [h2]
  by_cases h3 : BitVec.ofNat 32 b.header.bits = S.requiredBits <;> simp [h3]
  by_cases h4 : (b.header.time : Int) ≤ S.mtp <;> simp [h4]
  · omega
  by_cases h5 : now + MAX_FUTURE_BLOCK_TIME < (b.header.time : Int) <;> simp [h5]
  all_goals try omega
  all_goals (split <;> simp <;> omega)
