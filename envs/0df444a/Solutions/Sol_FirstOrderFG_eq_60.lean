-- Prove2me | solution 1 for FirstOrderFG.eq_60
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:35:29.15901+00:00
-- url     : https://prove2.me/submissions/037aa73b-8191-43f4-9ea5-2ffe8bd442fb

import Mathlib

theorem solution {K : ℕ} (p lh : Fin K → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (hl : ∀ j, 0 ≤ lh j) (η : ℝ) (hη : 0 < η) :
    let W := ∑ j, p j * Real.exp (-(η * lh j))
    Real.log W ≤ W - 1 ∧
      W - 1 ≤ -(η * ∑ j, p j * lh j) + η ^ 2 * ∑ j, p j * lh j ^ 2 / (1 + η * lh j) := by
  intro W
  have hWdef : W = ∑ j, p j * Real.exp (-(η * lh j)) := rfl
  have hterm : ∀ j, 0 ≤ p j * Real.exp (-(η * lh j)) :=
    fun j => mul_nonneg (hp j) (Real.exp_pos _).le
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun j _ => hterm j)
  have hWpos : 0 < W := by
    rcases hW0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).mp (hWdef ▸ h.symm)
      have hp0 : ∀ j, p j = 0 := by
        intro j
        have := hz j (Finset.mem_univ j)
        rcases mul_eq_zero.mp this with h' | h'
        · exact h'
        · exact absurd h' (Real.exp_pos _).ne'
      rw [Finset.sum_eq_zero (fun j _ => hp0 j)] at hp1
      exact zero_ne_one hp1
  refine ⟨Real.log_le_sub_one_of_pos hWpos, ?_⟩
  have key : ∀ j, p j * Real.exp (-(η * lh j)) - p j ≤
      -(η * (p j * lh j)) + η ^ 2 * (p j * lh j ^ 2 / (1 + η * lh j)) := by
    intro j
    have hx : 0 ≤ η * lh j := mul_nonneg hη.le (hl j)
    have hx1 : (0 : ℝ) < 1 + η * lh j := by linarith
    have h1 : Real.exp (-(η * lh j)) ≤ 1 - η * lh j + (η * lh j) ^ 2 / (1 + η * lh j) := by
      have e : 1 - η * lh j + (η * lh j) ^ 2 / (1 + η * lh j) = (1 + η * lh j)⁻¹ := by
        have := hx1.ne'
        first | (field_simp; ring) | field_simp
      rw [e, Real.exp_neg]
      exact inv_anti₀ hx1 (by linarith [Real.add_one_le_exp (η * lh j)])
    have h2 := mul_le_mul_of_nonneg_left h1 (hp j)
    have e2 : p j * (1 - η * lh j + (η * lh j) ^ 2 / (1 + η * lh j)) =
        p j - η * (p j * lh j) + η ^ 2 * (p j * lh j ^ 2 / (1 + η * lh j)) := by ring
    linarith
  have hL : W - 1 = ∑ j, (p j * Real.exp (-(η * lh j)) - p j) := by
    rw [Finset.sum_sub_distrib, hp1]
  have hR : -(η * ∑ j, p j * lh j) + η ^ 2 * ∑ j, p j * lh j ^ 2 / (1 + η * lh j) =
      ∑ j, (-(η * (p j * lh j)) + η ^ 2 * (p j * lh j ^ 2 / (1 + η * lh j))) := by
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hL, hR]
  exact Finset.sum_le_sum (fun j _ => key j)
