-- Prove2me | solution 1 for BitcoinBIP68.decode_sequence
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T01:55:02.713507+00:00
-- url     : https://prove2.me/submissions/aa21fcef-df16-4607-a48e-958f1fb63f00

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

open BitcoinBIP68

/-- Conjunction with a single power of two isolates that bit: the result is either `0` or
`2 ^ k`, according to bit `k` of `n`. -/
private theorem and_two_pow_eq (n k : Nat) : n &&& 2 ^ k = ((n / 2 ^ k) % 2) * 2 ^ k := by
  have h1 : (n &&& 2 ^ k) / 2 ^ k = (n / 2 ^ k) % 2 := by
    rw [Nat.and_div_two_pow, Nat.div_self (Nat.two_pow_pos k), Nat.and_one_is_mod]
  have h2 : (n &&& 2 ^ k) % 2 ^ k = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mod_self, Nat.and_zero]
  have h := Nat.div_add_mod (n &&& 2 ^ k) (2 ^ k)
  rw [h1, h2, Nat.add_zero, Nat.mul_comm] at h
  exact h.symm

theorem solution (sequence : BitVec 32) :
    (BitcoinBIP68.coreDisabled sequence = true ↔ BitcoinBIP68.specDisabled sequence) ∧
    (BitcoinBIP68.coreTimeBased sequence = true ↔ BitcoinBIP68.specTimeBased sequence) ∧
    BitcoinBIP68.coreDelay sequence = BitcoinBIP68.specDelay sequence ∧
    BitcoinBIP68.coreSeconds sequence = 512 * BitcoinBIP68.specDelay sequence := by
  have hlt : sequence.toNat < 4294967296 := sequence.isLt
  have h31 := and_two_pow_eq sequence.toNat 31
  have h22 := and_two_pow_eq sequence.toNat 22
  have h16 := Nat.and_two_pow_sub_one_eq_mod sequence.toNat 16
  simp only [Nat.reducePow, Nat.reduceSub] at h31 h22 h16
  have c31 : (0x80000000 : BitVec 32).toNat = 2147483648 := rfl
  have c22 : (0x00400000 : BitVec 32).toNat = 4194304 := rfl
  have c16 : (0x0000ffff : BitVec 32).toNat = 65535 := rfl
  have c0 : (0 : BitVec 32).toNat = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold coreDisabled specDisabled
    rw [bne_iff_ne, ne_eq, BitVec.toNat_eq, BitVec.toNat_and, c31, c0]
    constructor <;> intro h <;> omega
  · unfold coreTimeBased specTimeBased
    rw [bne_iff_ne, ne_eq, BitVec.toNat_eq, BitVec.toNat_and, c22, c0]
    constructor <;> intro h <;> omega
  · unfold coreDelay specDelay
    rw [BitVec.toNat_and, c16, h16]
  · unfold coreSeconds specDelay
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, c16, h16, Nat.shiftLeft_eq]
    have : sequence.toNat % 65536 < 65536 := Nat.mod_lt _ (by decide)
    omega
