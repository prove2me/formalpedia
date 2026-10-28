-- Prove2me | solution 1 for BitcoinMerkle.dup_leaf
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:03.283161+00:00
-- url     : https://prove2.me/submissions/6bc711f6-e36f-4ca1-bc33-c017e85c9daa

import Definitions.Def_BitcoinMerkle
import Theorems.Thm_BitcoinMerkle_rootLoop_fst
import Theorems.Thm_BitcoinMerkle_rootLoop_sticky
import Theorems.Thm_BitcoinMerkle_pairUp_append_even
import Theorems.Thm_BitcoinMerkle_hasEqualPair_append_even

open BitcoinMerkle

/-- One iteration of the loop. -/
private theorem rootLoop_step {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = BitcoinMerkle.rootLoop c z (BitcoinMerkle.pairUp c hs) (m || BitcoinMerkle.hasEqualPair hs) := by
  conv => lhs; rw [rootLoop]
  rw [dif_pos h]

/-- Level-0 form of CVE-2012-2459: duplicating the last leaf of an odd-length list leaves the
root unchanged, and the duplicate is detected. -/
theorem solution {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (l : List H) (a : H) (hne : l ≠ []) (heven : l.length % 2 = 0) :
    (BitcoinMerkle.computeMerkleRoot c z (l ++ [a])).1 = (BitcoinMerkle.computeMerkleRoot c z (l ++ [a, a])).1 ∧
    (BitcoinMerkle.computeMerkleRoot c z (l ++ [a, a])).2 = true := by
  have hlen : 0 < l.length := List.length_pos_iff.2 hne
  have hp : pairUp c (l ++ [a]) = pairUp c (l ++ [a, a]) := by
    rw [BitcoinMerkle.pairUp_append_even c l [a] heven, BitcoinMerkle.pairUp_append_even c l [a, a] heven]
    simp [pairUp]
  have hq : hasEqualPair (l ++ [a, a]) = true := by
    rw [BitcoinMerkle.hasEqualPair_append_even l [a, a] heven]
    simp [hasEqualPair]
  have h1 : 1 < (l ++ [a]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have h2 : 1 < (l ++ [a, a]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  unfold computeMerkleRoot
  constructor
  · rw [rootLoop_step c z _ false h1, rootLoop_step c z _ false h2, hp]
    exact BitcoinMerkle.rootLoop_fst c z _ _ _
  · rw [rootLoop_step c z _ false h2, hq]
    simp only [Bool.or_true]
    exact BitcoinMerkle.rootLoop_sticky c z _
