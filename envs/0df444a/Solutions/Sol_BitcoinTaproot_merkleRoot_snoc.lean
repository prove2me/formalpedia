-- Prove2me | solution 1 for BitcoinTaproot.merkleRoot_snoc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:36:10.067983+00:00
-- url     : https://prove2.me/submissions/c544a45e-d640-4083-8d62-e6b36bf28a9b

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem S190TAP_go_snoc (node : Bytes) (hn : node.length = TAPROOT_CONTROL_NODE_SIZE) :
    ∀ (k : Nat) (s : Bytes), s.length = TAPROOT_CONTROL_NODE_SIZE * k →
      controlNodes.go (k + 1) (s ++ node) = controlNodes.go k s ++ [node]
  | 0, s, hs => by
    have : s = [] := List.eq_nil_of_length_eq_zero (by simpa using hs)
    subst this
    simp [controlNodes.go, ← hn]
  | k + 1, s, hs => by
    have hlen : TAPROOT_CONTROL_NODE_SIZE ≤ s.length := by
      rw [hs, Nat.mul_succ]; omega
    have h1 : (s ++ node).take TAPROOT_CONTROL_NODE_SIZE = s.take TAPROOT_CONTROL_NODE_SIZE :=
      List.take_append_of_le_length hlen
    have h2 : (s ++ node).drop TAPROOT_CONTROL_NODE_SIZE = s.drop TAPROOT_CONTROL_NODE_SIZE ++ node :=
      List.drop_append_of_le_length hlen
    have h3 : (s.drop TAPROOT_CONTROL_NODE_SIZE).length = TAPROOT_CONTROL_NODE_SIZE * k := by
      rw [List.length_drop, hs, Nat.mul_succ]; omega
    rw [controlNodes.go, h1, h2, S190TAP_go_snoc node hn k _ h3]
    simp [controlNodes.go]

theorem solution (control node leaf : Bytes)
    (hc : BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE ≤ control.length)
    (hm : (control.length - BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE) % BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE = 0)
    (hn : node.length = BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE) :
    BitcoinTaproot.taprootMerkleRoot (control ++ node) leaf =
      BitcoinTaproot.tapbranchHash (BitcoinTaproot.taprootMerkleRoot control leaf) node := by
  unfold taprootMerkleRoot controlNodes
  simp only [TAPROOT_CONTROL_BASE_SIZE, TAPROOT_CONTROL_NODE_SIZE] at hc hm hn ⊢
  have hlen : (control ++ node).length - 33 = (control.length - 33) + 32 := by
    simp [List.length_append, hn]; omega
  have hk : ((control ++ node).length - 33) / 32 = (control.length - 33) / 32 + 1 := by
    rw [hlen]; omega
  have hd : (control ++ node).drop 33 = control.drop 33 ++ node := List.drop_append_of_le_length hc
  have hs : (control.drop 33).length = TAPROOT_CONTROL_NODE_SIZE * ((control.length - 33) / 32) := by
    simp only [List.length_drop, TAPROOT_CONTROL_NODE_SIZE]; omega
  rw [hk, hd, S190TAP_go_snoc node hn _ _ hs, List.foldl_append]
  rfl
