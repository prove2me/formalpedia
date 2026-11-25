-- Prove2me | solution 1 for ConjCoord.Proof.card_zfilter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:46:52.768977+00:00
-- url     : https://prove2.me/submissions/8f1fc00b-a2cc-4593-b089-4f3f2baf824b

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Compute

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution (c : ℕ) (hc : 0 < c) (n : ℕ) (r : ℤ) (hr : r ≤ n) :
    ((Icc (-(n : ℤ)) n).filter fun z => (c : ℤ) * z ^ 2 = r).card =
      if 0 ≤ r then zc c r.toNat else 0 := by
  split_ifs with h0
  · obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s := ⟨r.toNat, (Int.toNat_of_nonneg h0).symm⟩
    simp only [Int.toNat_natCast]
    have hsn : s ≤ n := by exact_mod_cast hr
    unfold zc
    by_cases hs : s % c = 0 ∧ Nat.sqrt (s / c) * Nat.sqrt (s / c) = s / c
    · rw [if_pos hs]
      set t := Nat.sqrt (s / c) with ht
      have hct : c * (t * t) = s := by
        rw [hs.2]; exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hs.1)
      have hts : t ≤ s :=
        calc t ≤ t * t := Nat.le_mul_self t
          _ ≤ c * (t * t) := Nat.le_mul_of_pos_left _ hc
          _ = s := hct
      have hctZ : (c : ℤ) * (t : ℤ) ^ 2 = s := by
        rw [← hct]; push_cast; ring
      have key : ∀ z : ℤ, (c : ℤ) * z ^ 2 = s ↔ z = t ∨ z = -t := by
        intro z
        rw [← hctZ]
        constructor
        · intro h
          have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
          have := mul_left_cancel₀ hc0 h
          exact sq_eq_sq_iff_eq_or_eq_neg.mp this
        · rintro (rfl | rfl) <;> ring
      have hfil : ((Icc (-(n : ℤ)) n).filter fun z => (c : ℤ) * z ^ 2 = s) =
          {(t : ℤ), -(t : ℤ)} := by
        ext z
        simp only [mem_filter, mem_Icc, key, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl) <;> refine ⟨⟨by omega, by omega⟩, by simp⟩
      rw [hfil]
      split_ifs with hs0
      · have : t = 0 := by
          rcases Nat.eq_zero_of_le_zero (hts.trans hs0.le) with h; exact h
        simp [this]
      · have ht0 : t ≠ 0 := by
          rintro h; apply hs0; rw [← hct, h]; simp
        rw [card_insert_of_notMem (by simp; omega), card_singleton]
    · rw [if_neg hs]
      rw [card_eq_zero, filter_eq_empty_iff]
      intro z _ h
      apply hs
      have hz : c * (z.natAbs * z.natAbs) = s := by
        have : ((c * (z.natAbs * z.natAbs) : ℕ) : ℤ) = s := by
          push_cast; rw [abs_mul_abs_self, ← h]; ring
        exact_mod_cast this
      refine ⟨?_, ?_⟩
      · rw [← hz]; exact Nat.mul_mod_right _ _
      · rw [← hz, Nat.mul_div_cancel_left _ hc, Nat.sqrt_eq]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro z _ h
    have : (0 : ℤ) ≤ (c : ℤ) * z ^ 2 := by positivity
    omega
end ConjCoord.Proof
