-- Prove2me | solution 1 for FixedNumerator.QuarticData.invert_two_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:47.676031+00:00
-- url     : https://prove2.me/submissions/bbf9301e-b624-4b35-a910-0d605bca77c6

module
public import Definitions.Def_FixedNumerator_Split
public import Definitions.Def_FixedNumerator_Cases

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator
open FixedNumerator.QuarticData
variable (D : QuarticData)
namespace FixedNumerator.QuarticData
theorem _root_.solution (S T : ℕ → ℂ) (a : ℂ) {M : ℕ} (hM : 2 ≤ M) (hT0 : T 0 = 0)
    (h : ∀ Y, S Y = T Y + a * T (Y / M)) :
    ∀ X n, X + 1 ≤ n → T X = ∑ j ∈ range n, (-a) ^ j * S (X / M ^ j) := by
  have hS0 : S 0 = 0 := by rw [h 0, Nat.zero_div, hT0]; ring
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.div_one, one_mul]
    rcases Nat.eq_zero_or_pos X with hX | hX
    · subst hX
      rw [hT0, hS0]
      simp [hS0]
    · have hlt : X / M < X := Nat.div_lt_self hX (by omega)
      have hle : X / M + 1 ≤ n' := by
        have : X / M ≤ X / 2 := Nat.div_le_div_left hM (by norm_num)
        omega
      have hT : T X = S X - a * T (X / M) := by rw [h X]; ring
      rw [hT, ih (X / M) hlt n' hle, Finset.mul_sum]
      rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      ring
end FixedNumerator.QuarticData
