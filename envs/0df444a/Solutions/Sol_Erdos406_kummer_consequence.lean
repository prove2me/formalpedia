-- Prove2me | solution 1 for Erdos406.kummer_consequence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T01:45:54.55403+00:00
-- url     : https://prove2.me/submissions/c79d2d17-b89a-481c-ac55-486a1dcb366a

import Mathlib

namespace S75KC

lemma key : ∀ m : ℕ, (∀ i, 2 * (m % 3 ^ i) < 3 ^ i) → Nat.digits 3 m ⊆ [0, 1] := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rw [Nat.digits_def' (by norm_num) hm]
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have := h 1
      simp at this
      have : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
      simp; omega
    · refine ih (m / 3) (Nat.div_lt_self hm (by norm_num)) ?_ hx
      intro i
      have h1 := h (i + 1)
      rw [pow_succ', Nat.mod_mul] at h1
      omega

end S75KC

theorem solution
    (h : { n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }.Finite) :
    ∀ᶠ k : ℕ in Filter.atTop, 3 ∣ Nat.choose (2 ^ (k + 1)) (2 ^ k) := by
  have hT : {k : ℕ | 2 ^ k ∈ { n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }}.Finite :=
    h.preimage (fun a _ b _ hab => Nat.pow_right_injective le_rfl hab)
  obtain ⟨N, hN⟩ := hT.bddAbove
  refine Filter.eventually_atTop.2 ⟨N + 1, fun k hk => ?_⟩
  have hkT : k ∉ {k : ℕ | 2 ^ k ∈ { n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }} := by
    intro hm; have := hN hm; omega
  have hd : ¬ Nat.digits 3 (2 ^ k) ⊆ [0, 1] := by
    intro hd; exact hkT ⟨⟨k, rfl⟩, hd⟩
  have : ∃ i, 3 ^ i ≤ 2 * (2 ^ k % 3 ^ i) := by
    by_contra hc; push Not at hc; exact hd (S75KC.key _ hc)
  obtain ⟨i, hi⟩ := this
  have hi0 : i ≠ 0 := by rintro rfl; simp [Nat.mod_one] at hi
  set m := 2 ^ k with hm
  have hc : 2 ^ (k + 1) = m + m := by rw [hm, pow_succ]; ring
  rw [hc]
  apply dvd_of_one_le_padicValNat
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [padicValNat_choose' (b := max (i + 1) (Nat.log 3 (m + m) + 1)) (by omega)]
  apply Finset.card_pos.2
  refine ⟨i, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨by omega, by omega⟩, by omega⟩
