-- Prove2me | solution 1 for BlockCycleRotation.tsum_pTerm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:37:58.63441+00:00
-- url     : https://prove2.me/submissions/69bf52b3-a992-412c-bbcd-717409717d07

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open Real Finset Filter Topology

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem pTerm_pos (q : ℕ × ℕ) : 0 < pTerm q := by
  unfold pTerm; positivity

end BlockCycleRotation

open BlockCycleRotation in
/-- **`∑ pTerm = ζ(2,1)`**: the reindexing `(i,j) ↦ (a,a') = (i+j+2, i+1)`. -/
theorem solution : ∑' p : ℕ × ℕ, zTerm p = ∑' q : ℕ × ℕ, pTerm q:= by
  refine tsum_eq_tsum_of_ne_zero_bij (fun q => (q.1.1 + q.1.2 + 2, q.1.1 + 1)) ?_ ?_ ?_
  · intro x y heq
    obtain ⟨⟨i, j⟩, hx⟩ := x
    obtain ⟨⟨i', j'⟩, hy⟩ := y
    simp only [Prod.mk.injEq] at heq
    have hij : i = i' ∧ j = j' := by omega
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    exact ⟨hij.1, hij.2⟩
  · rintro ⟨p1, p2⟩ hp
    simp only [Function.mem_support, ne_eq] at hp
    have hz : 1 ≤ p2 ∧ p2 < p1 := by
      unfold zTerm at hp
      split_ifs at hp with hc
      · exact hc
      · exact absurd rfl hp
    refine ⟨⟨(p2 - 1, p1 - p2 - 1), ?_⟩, ?_⟩
    · simp only [Function.mem_support, ne_eq]
      exact ne_of_gt (pTerm_pos _)
    · simp only [Prod.mk.injEq]
      omega
  · rintro ⟨⟨i, j⟩, -⟩
    change zTerm (i + j + 2, i + 1) = pTerm (i, j)
    unfold zTerm pTerm
    rw [if_pos (by omega)]
    push_cast
    ring_nf
