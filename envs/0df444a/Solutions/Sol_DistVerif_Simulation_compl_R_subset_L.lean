-- Prove2me | solution 1 for DistVerif.Simulation.compl_R_subset_L
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-27T02:34:52.530204+00:00
-- url     : https://prove2.me/submissions/ff0ca7e1-4996-48ee-ae17-2644c2d5cddf

import Mathlib
import Definitions.Def_DistVerif_Simulation_Network

open DistVerif.Simulation

/-- Proof of `compl_R_subset_L`: every vertex outside `R_{t-1}` is in `L_{t-1}` and vice versa.
A tree node `u^ℓ_k` covers the leaf interval `[k·D, k·D + D - 1]` with `D = d^(p-ℓ)`; if it misses
`R_i` its leftmost leaf is `< i`, hence far left of `d^p - i`; symmetrically for `L_i`. -/
theorem solution (Γ d p t : ℕ) (ht0 : 0 < t) (ht : (t : ℝ) < ((d : ℝ) ^ p - 1) / 2) :
    (R Γ d p (t - 1))ᶜ ⊆ L Γ d p (t - 1) ∧ (L Γ d p (t - 1))ᶜ ⊆ R Γ d p (t - 1) := by
  -- Turn the real-valued round bound into `2t + 1 < d^p` over ℕ.
  have hN : 2 * t + 1 < d ^ p := by
    have h1 : ((2 * t + 1 : ℕ) : ℝ) < ((d ^ p : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h1
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp; simp at hN
      · rw [zero_pow hp.ne'] at hN; omega
    · exact h
  have hDpos : ∀ ℓ : ℕ, 0 < d ^ (p - ℓ) := fun ℓ => pow_pos hdpos _
  -- The leaves below `u^ℓ_k` form the block `[k·D, (k+1)·D)` inside `[0, d^p)`.
  have hD : ∀ ℓ : Fin (p + 1), ∀ k : Fin (d ^ (ℓ : ℕ)),
      (k : ℕ) * d ^ (p - ℓ) + d ^ (p - ℓ) ≤ d ^ p := by
    intro ℓ k
    have hl : (ℓ : ℕ) ≤ p := Nat.lt_succ_iff.mp ℓ.isLt
    have hsplit : d ^ p = d ^ (ℓ : ℕ) * d ^ (p - ℓ) := by
      rw [← pow_add, Nat.add_sub_cancel' hl]
    rw [hsplit, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ k.isLt
  have hdiv1 : ∀ k D : ℕ, 0 < D → k * D / D = k := fun k D hD => Nat.mul_div_cancel k hD
  have hdiv2 : ∀ k D : ℕ, 0 < D → (k * D + (D - 1)) / D = k := by
    intro k D hD
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt (by omega), zero_add]
  refine ⟨?_, ?_⟩
  · -- `V \ R_{t-1} ⊆ L_{t-1}`
    intro v hv
    simp only [Finset.mem_compl, R, L, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rcases v with ⟨a, j⟩ | ⟨ℓ, k⟩
    · simp only [InRight, InLeft] at hv ⊢
      right; omega
    · simp only [InRight, InLeft] at hv ⊢
      by_cases h0 : t - 1 = 0
      · -- `v = s`, and `s ≠ r` because `d^p > 1`.
        simp only [h0, if_true, not_not] at hv ⊢
        omega
      · simp only [h0, if_false] at hv ⊢
        have hb := hD ℓ k
        have hp := hDpos ℓ
        refine ⟨⟨(k : ℕ) * d ^ (p - ℓ), by omega⟩, ?_, hdiv1 _ _ hp⟩
        by_contra hc
        exact hv ⟨⟨(k : ℕ) * d ^ (p - ℓ), by omega⟩, by simp only at hc ⊢; omega, hdiv1 _ _ hp⟩
  · -- `V \ L_{t-1} ⊆ R_{t-1}`
    intro v hv
    simp only [Finset.mem_compl, R, L, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rcases v with ⟨a, j⟩ | ⟨ℓ, k⟩
    · simp only [InRight, InLeft] at hv ⊢
      omega
    · simp only [InRight, InLeft] at hv ⊢
      by_cases h0 : t - 1 = 0
      · -- `v = r`, and `r ≠ s` because `d^p > 1`.
        simp only [h0, if_true, not_not] at hv ⊢
        omega
      · simp only [h0, if_false] at hv ⊢
        have hb := hD ℓ k
        have hp := hDpos ℓ
        refine ⟨⟨(k : ℕ) * d ^ (p - ℓ) + (d ^ (p - ℓ) - 1), by omega⟩, ?_, hdiv2 _ _ hp⟩
        by_contra hc
        exact hv ⟨⟨(k : ℕ) * d ^ (p - ℓ) + (d ^ (p - ℓ) - 1), by omega⟩, by simp only at hc ⊢; omega,
          hdiv2 _ _ hp⟩
