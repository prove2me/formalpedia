-- Prove2me | solution 1 for BitcoinPow.overflow_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:36:52.916321+00:00
-- url     : https://prove2.me/submissions/a646e7a7-ed94-4fc0-be59-0fdfdcc58fee

import Definitions.Def_BitcoinPow

open BitcoinPow

private theorem compactSize_lt (c : BitVec 32) : compactSize c < 256 := by
  unfold compactSize
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := c.isLt
  omega

private theorem compactWord_lt (c : BitVec 32) : compactWord c < 2 ^ 23 := by
  unfold compactWord
  rw [BitVec.toNat_and]
  have h : (0x007fffff : BitVec 32).toNat = 2 ^ 23 - 1 := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

private theorem pow256_eq (k : Nat) : (256 : Nat) ^ k = 2 ^ (8 * k) := by
  rw [Nat.pow_mul]

theorem solution (c : BitVec 32) :
    BitcoinPow.compactOverflow c = true ↔ BitcoinPow.width ≤ BitcoinPow.specTarget c := by
  unfold compactOverflow specTarget width
  have hS := compactSize_lt c
  have hW := compactWord_lt c
  generalize compactSize c = S at *
  generalize compactWord c = W at *
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  by_cases h3 : S ≤ 3
  · rw [if_pos h3]
    have hle : W / 256 ^ (3 - S) ≤ W := Nat.div_le_self _ _
    have h23 : (2 : Nat) ^ 23 < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) (by decide)
    constructor
    · intro h
      obtain ⟨-, (h | h) | h⟩ := h
      · omega
      · omega
      · omega
    · intro h; omega
  · rw [if_neg h3]
    rcases Nat.lt_or_ge S 33 with h32 | h33
    · -- S ≤ 32: no overflow either way
      have hpow : 256 ^ (S - 3) ≤ 256 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
      have hprod : W * 256 ^ (S - 3) ≤ 2 ^ 23 * 256 ^ 29 :=
        Nat.mul_le_mul (Nat.le_of_lt hW) hpow
      have hlt : 2 ^ 23 * 256 ^ 29 < 2 ^ 256 := by
        rw [pow256_eq, ← Nat.pow_add]
        exact Nat.pow_lt_pow_right (by decide) (by decide)
      constructor
      · intro h
        obtain ⟨-, (h | h) | h⟩ := h
        · omega
        · omega
        · omega
      · intro h; omega
    · rcases Nat.lt_or_ge S 35 with h34 | h35
      · rcases Nat.lt_or_ge S 34 with h33' | h34'
        · -- S = 33
          have hS33 : S = 33 := by omega
          subst hS33
          have h240 : (256 : Nat) ^ (33 - 3) = 2 ^ 240 := by rw [pow256_eq]
          rw [h240]
          have hsplit : (2 : Nat) ^ 256 = 2 ^ 16 * 2 ^ 240 := by rw [← Nat.pow_add]
          constructor
          · intro h
            obtain ⟨hW0, (h | h) | h⟩ := h
            · omega
            · omega
            · rw [hsplit]
              exact Nat.mul_le_mul_right _ (by omega)
          · intro h
            refine ⟨?_, Or.inr ⟨?_, by decide⟩⟩
            · intro hW0; subst hW0; simp at h
            · rcases Nat.lt_or_ge 0xffff W with hgt | hle
              · exact hgt
              · exfalso
                have h1 : W * 2 ^ 240 ≤ 0xffff * 2 ^ 240 := Nat.mul_le_mul_right _ hle
                have h2 : 0xffff * 2 ^ 240 < 2 ^ 16 * 2 ^ 240 := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.two_pow_pos _)
                omega
        · -- S = 34
          have hS34 : S = 34 := by omega
          subst hS34
          have h248 : (256 : Nat) ^ (34 - 3) = 2 ^ 248 := by rw [pow256_eq]
          rw [h248]
          have hsplit : (2 : Nat) ^ 256 = 2 ^ 8 * 2 ^ 248 := by rw [← Nat.pow_add]
          constructor
          · intro h
            obtain ⟨hW0, (h | h) | h⟩ := h
            · omega
            · rw [hsplit]; exact Nat.mul_le_mul_right _ (by omega)
            · rw [hsplit]; exact Nat.mul_le_mul_right _ (by omega)
          · intro h
            refine ⟨?_, Or.inl (Or.inr ⟨?_, by decide⟩)⟩
            · intro hW0; subst hW0; simp at h
            · rcases Nat.lt_or_ge 0xff W with hgt | hle
              · exact hgt
              · exfalso
                have h1 : W * 2 ^ 248 ≤ 0xff * 2 ^ 248 := Nat.mul_le_mul_right _ hle
                have h2 : 0xff * 2 ^ 248 < 2 ^ 8 * 2 ^ 248 := Nat.mul_lt_mul_of_pos_right (by decide) (Nat.two_pow_pos _)
                omega
      · -- S ≥ 35
        have hpow : 2 ^ 256 ≤ 256 ^ (S - 3) := by
          rw [pow256_eq]
          exact Nat.pow_le_pow_right (by decide) (by omega)
        constructor
        · intro h
          obtain ⟨hW0, -⟩ := h
          calc 2 ^ 256 ≤ 256 ^ (S - 3) := hpow
            _ = 1 * 256 ^ (S - 3) := (Nat.one_mul _).symm
            _ ≤ W * 256 ^ (S - 3) := Nat.mul_le_mul_right _ (by omega)
        · intro h
          refine ⟨?_, Or.inl (Or.inl (by omega))⟩
          intro hW0; subst hW0; simp at h
