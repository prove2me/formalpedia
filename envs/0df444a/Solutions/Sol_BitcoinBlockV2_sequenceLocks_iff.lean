-- Prove2me | solution 1 for BitcoinBlockV2.sequenceLocks_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:13:10.551898+00:00
-- url     : https://prove2.me/submissions/1d9ef157-9806-4a29-85c3-4245fe4d04d4

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

section S190BLK_sec68
open BitcoinBIP68

theorem S190BLK_delay (s : BitVec 32) : coreDelay s = specDelay s := by
  unfold coreDelay specDelay
  rw [BitVec.toNat_and]
  have : (0x0000ffff : BitVec 32).toNat = 2^16 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem S190BLK_and_pow (x i : Nat) : x &&& 2 ^ i = 2 ^ i * (x / 2 ^ i % 2) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  have h := Nat.mod_two_eq_zero_or_one (x / 2 ^ i)
  rcases h with h | h
  · rw [h, Nat.mul_zero, Nat.zero_testBit]
    by_cases hij : i = j
    · subst hij; simp [Nat.testBit_eq_decide_div_mod_eq, h]
    · simp [hij]
  · rw [h, Nat.mul_one, Nat.testBit_two_pow]
    by_cases hij : i = j
    · subst hij; simp [Nat.testBit_eq_decide_div_mod_eq, h]
    · simp [hij]

theorem S190BLK_bit (s : BitVec 32) (i : Nat) (hi : i < 32) :
    ((s &&& BitVec.ofNat 32 (2 ^ i)) != 0) = true ↔ s.toNat / 2 ^ i % 2 = 1 := by
  have e : (BitVec.ofNat 32 (2 ^ i)).toNat = 2 ^ i := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; exact Nat.pow_lt_pow_right (by decide) hi
  rw [bne_iff_ne, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_and, e, S190BLK_and_pow, show BitVec.toNat (0 : BitVec 32) = 0 from rfl]
  have h := Nat.mod_two_eq_zero_or_one (s.toNat / 2 ^ i)
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  rcases h with h | h <;> simp [h] <;> omega

theorem S190BLK_dis (s : BitVec 32) : coreDisabled s = true ↔ specDisabled s := by
  unfold coreDisabled specDisabled
  have := S190BLK_bit s 31 (by decide)
  have hl := s.isLt
  have : s.toNat / 2^31 < 2 := by omega
  rw [show (0x80000000 : BitVec 32) = BitVec.ofNat 32 (2^31) by decide, S190BLK_bit s 31 (by decide)]
  omega

theorem S190BLK_tb (s : BitVec 32) : coreTimeBased s = true ↔ specTimeBased s := by
  unfold coreTimeBased specTimeBased
  rw [show (0x00400000 : BitVec 32) = BitVec.ofNat 32 (2^22) by decide, S190BLK_bit s 22 (by decide)]

theorem S190BLK_sec (s : BitVec 32) : coreSeconds s = 512 * specDelay s := by
  unfold coreSeconds specDelay
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and]
  have : (0x0000ffff : BitVec 32).toNat = 2^16 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
  have := Nat.mod_lt s.toNat (show 0 < 2^16 by decide)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem S190BLK_en (v f : BitVec 32) : coreEnabled v f = true ↔ specEnabled v f := by
  unfold coreEnabled specEnabled
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 (2^0) by decide]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [S190BLK_bit f 0 (by decide)]
  simp

def S190BLK_P (ctx : Context) (acc : Accumulator) : Prop :=
  acc.minHeight < (ctx.height : Int) ∧ acc.minTime < (ctx.mtp (ctx.height - 1) : Int)

theorem S190BLK_step (ctx : Context) (acc : Accumulator) (i : Input) :
    S190BLK_P ctx (coreStep ctx acc i) ↔ S190BLK_P ctx acc ∧ inputSatisfied ctx i := by
  unfold coreStep inputSatisfied S190BLK_P
  by_cases hd : coreDisabled i.sequence = true
  · have : specDisabled i.sequence := (S190BLK_dis _).mp hd
    simp [hd, this]
  · have hd' : ¬ specDisabled i.sequence := fun h => hd ((S190BLK_dis _).mpr h)
    by_cases ht : coreTimeBased i.sequence = true
    · have ht' : specTimeBased i.sequence := (S190BLK_tb _).mp ht
      simp only [hd, ht, if_true, Bool.false_eq_true, if_false, hd', ht', false_or, S190BLK_sec]
      simp only [Int.max_lt]
      omega
    · have ht' : ¬ specTimeBased i.sequence := fun h => ht ((S190BLK_tb _).mpr h)
      simp only [hd, ht, Bool.false_eq_true, if_false, hd', ht', false_or, S190BLK_delay]
      simp only [Int.max_lt]
      omega

theorem S190BLK_fold (ctx : Context) (l : List Input) (acc : Accumulator) :
    S190BLK_P ctx (l.foldl (coreStep ctx) acc) ↔ S190BLK_P ctx acc ∧ ∀ i ∈ l, inputSatisfied ctx i := by
  induction l generalizing acc with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons, ih, S190BLK_step]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, b, c⟩
    · rintro ⟨a, b, c⟩; exact ⟨⟨a, b⟩, c⟩

theorem S190BLK_seq (version flags : BitVec 32) (ctx : Context) (inputs : List Input) :
    sequenceLocks version flags ctx inputs = true ↔ satisfiesBIP68 version flags ctx inputs := by
  unfold sequenceLocks calculate satisfiesBIP68
  have hinit : S190BLK_P ctx initial := by
    unfold S190BLK_P initial; constructor <;> simp <;> omega
  by_cases he : coreEnabled version flags = true
  · have he' : specEnabled version flags := (S190BLK_en _ _).mp he
    rw [if_pos he]
    have := S190BLK_fold ctx inputs initial
    unfold S190BLK_P at this hinit
    simp only [evaluate, decide_eq_true_eq, he', not_true_eq_false, false_or]
    rw [this]; simp [hinit]
  · have he' : ¬ specEnabled version flags := fun h => he ((S190BLK_en _ _).mpr h)
    rw [if_neg he]
    unfold S190BLK_P initial at hinit
    simp only [evaluate, decide_eq_true_eq, he', not_false_eq_true, true_or, iff_true]
    exact hinit

end S190BLK_sec68

open BitcoinBlockV2 in
theorem solution (u : Ledger) (height : Nat) (mtp : Nat → Nat) (ltf : Nat) (tx : BitcoinSer.Tx) :
    BitcoinBlockV2.sequenceLocksOk u height mtp ltf tx = true ↔
      BitcoinBIP68.satisfiesBIP68 (BitVec.ofNat 32 tx.version) (BitVec.ofNat 32 ltf) ⟨height, mtp⟩
        (tx.vin.map fun i => ⟨BitVec.ofNat 32 i.nSequence, (BitcoinBlockV2.accessCoin u i.prevout).height⟩) :=
  S190BLK_seq _ _ _ _
