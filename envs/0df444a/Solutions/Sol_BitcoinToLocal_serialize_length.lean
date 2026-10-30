-- Prove2me | solution 1 for BitcoinToLocal.serialize_length
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:18:58.409193+00:00
-- url     : https://prove2.me/submissions/5df4fac0-6f71-471e-af47-2ea98badcaf7

import Definitions.Def_BitcoinToLocal
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinVerify_p2wsh_correct

open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

private theorem natBytes_length : ∀ (k n : Nat), n < 256 ^ k → (natBytes n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this; rw [natBytes]; simp
  | k + 1, n, h => by
    rw [natBytes]
    split
    · simp
    · simp only [List.length_cons]
      have := natBytes_length k (n / 256) (by rw [Nat.pow_succ] at h; omega)
      omega

/-- A script number of magnitude below `2^(8k)` serializes to at most `k + 1` bytes. -/
theorem solution (n : Int) (k : Nat) (h : n.natAbs < 256 ^ k) :
    (BitcoinScript.serialize n).length ≤ k + 1 := by
  unfold serialize
  split
  · simp
  · have hm := natBytes_length k n.natAbs h
    dsimp only
    split
    · simp only [List.length_append, List.length_singleton]; omega
    · split
      · have : ∀ l : Bytes, (setTop l).length = l.length := by
          intro l; induction l with
          | nil => rfl
          | cons b r ih => cases r with
            | nil => rfl
            | cons c r' => simp only [setTop, List.length_cons] at ih ⊢; omega
        rw [this]; omega
      · omega
