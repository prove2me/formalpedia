-- Prove2me | solution 2 for BitcoinTaproot.merkleRoot_snoc
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T16:58:08.839237+00:00
-- url     : https://prove2.me/submissions/8ebd4386-3f8a-4065-bf52-e2b9a3174ed1

import Definitions.Def_BitcoinTaproot

open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

private theorem lexLt_asymm : ∀ (a b : Bytes), lexLt a b = true → lexLt b a = false
  | [], [], h => by simp [lexLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [lexLt] at h
  | x :: xs, y :: ys, h => by
    simp only [lexLt] at h ⊢
    by_cases h1 : x.toNat < y.toNat
    · rw [if_neg (by omega), if_pos h1]
    · rw [if_neg h1] at h
      by_cases h2 : y.toNat < x.toNat
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        rw [if_neg h2, if_neg h1]
        exact lexLt_asymm xs ys h

private theorem lexLt_total : ∀ (a b : Bytes), lexLt a b = false → lexLt b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [lexLt] at h
  | _ :: _, [], _, h => by simp [lexLt] at h
  | x :: xs, y :: ys, h1, h2 => by
    simp only [lexLt] at h1 h2
    by_cases hxy : x.toNat < y.toNat
    · rw [if_pos hxy] at h1; cases h1
    · rw [if_neg hxy] at h1
      by_cases hyx : y.toNat < x.toNat
      · rw [if_pos hyx] at h2; cases h2
      · rw [if_neg hyx] at h1
        rw [if_neg hyx, if_neg hxy] at h2
        have hx : x = y := by
          have : x.toNat = y.toNat := by omega
          exact BitVec.eq_of_toNat_eq this
        rw [hx, lexLt_total xs ys h1 h2]

/-- Appending a 32-byte node to a control block hashes the current root with that node. -/
theorem solution (control node leaf : Bytes)
    (hc : BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE ≤ control.length)
    (hm : (control.length - BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE) % BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE = 0)
    (hn : node.length = BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE) :
    BitcoinTaproot.taprootMerkleRoot (control ++ node) leaf =
      BitcoinTaproot.tapbranchHash (BitcoinTaproot.taprootMerkleRoot control leaf) node := by
  unfold taprootMerkleRoot controlNodes
  unfold TAPROOT_CONTROL_BASE_SIZE TAPROOT_CONTROL_NODE_SIZE at *
  have e1 : ∀ (n : Nat) (t : Bytes), controlNodes.go (n + 1) t = t.take 32 :: controlNodes.go n (t.drop 32) :=
    fun n t => rfl
  have key : ∀ (k : Nat) (s : Bytes), s.length = k * 32 →
      controlNodes.go (k + 1) (s ++ node) = controlNodes.go k s ++ [node] := by
    intro k
    induction k with
    | zero =>
      intro s hs
      have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rw [e1, List.nil_append, List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
      rfl
    | succ k ih =>
      intro s hs
      rw [e1 (k + 1) (s ++ node), e1 k s]
      have hl : 32 ≤ s.length := by omega
      rw [List.take_append_of_le_length hl, List.drop_append_of_le_length hl, ih (s.drop 32) (by simp; omega)]
      rfl
  simp only [List.length_append, hn]
  rw [show (control.length + 32 - 33) / 32 = (control.length - 33) / 32 + 1 by omega]
  rw [List.drop_append_of_le_length hc]
  rw [key _ _ (by simp; omega)]
  simp [List.foldl_append]
