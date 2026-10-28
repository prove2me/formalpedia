-- Prove2me | solution 1 for BitcoinBlockV2.work_increases
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:22:54.543915+00:00
-- url     : https://prove2.me/submissions/f738e54f-c2ba-4d62-a224-79c370df3580

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

open BitcoinBlockV2 in
theorem S190BLK_ah_pow (S : ChainState) (h : BitcoinSer.Header) (now : Int) (S0 : ChainState) (u0 : BlockUndo)
    (hA : acceptHeader S h now = .accept S0 u0) : checkHeaderPow h = true := by
  unfold acceptHeader at hA
  cases hp : checkHeaderPow h
  · simp [hp] at hA
  · rfl

open BitcoinBlockV2 in
theorem S190BLK_val_acc (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : validate S b now = .accept S' undo) :
    checkHeaderPow b.header = true ∧ checkBlock b = true ∧ contextualCheckBlock S b = true ∧
    connectBlock S b = some (S'.utxo, undo) ∧ S' = ⟨S.headers ++ [b.header], S'.utxo⟩ := by
  unfold validate at h
  split at h
  · rename_i S0 u0 hA
    have hp := S190BLK_ah_pow _ _ _ _ _ hA
    by_cases c1 : checkBlock b = true
    · by_cases c2 : contextualCheckBlock S b = true
      · simp only [c1, c2, Bool.not_true, Bool.false_eq_true, if_false] at h
        split at h
        · cases h
        · rename_i u un hc
          cases h
          exact ⟨hp, c1, c2, hc, rfl⟩
      · simp [c1, c2] at h
    · simp [c1] at h
  · rename_i o hno
    exact absurd h (hno S' undo)

open BitcoinBlockV2 in
theorem solution (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) : S.chainWork < S'.chainWork := by
  obtain ⟨hp, -, -, -, hS⟩ := S190BLK_val_acc S b now S' undo h
  rw [hS]
  unfold ChainState.chainWork
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have : 0 < blockProof b.header.bits := by
    unfold checkHeaderPow BitcoinPow.checkProofOfWork at hp
    unfold blockProof
    split at hp
    · cases hp
    · rename_i t ht
      rw [ht]; exact Nat.succ_pos _
  omega
