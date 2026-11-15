-- Prove2me | solution 1 for DiazModulus.dalag_cor_12_21
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:32:16.273196+00:00
-- url     : https://prove2.me/submissions/1d01c9b2-6a7f-436d-a1d7-30aff663aa1e

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rank_bound

open Complex ComplexConjugate

/-! # DALAG Corollary 12.21: a lower bound for the rank of a matrix over `ℒ̃`

If `d = 0` there is nothing to prove. Otherwise Roy's Corollary 1 (DALAG Th. 12.20) gives `P ∈ GL_d(Q̄)`,
`Q ∈ GL_ℓ(Q̄)` and `1 ≤ d' ≤ d`, `ℓ' ≤ ℓ` with `(PMQ)ᵢⱼ = 0` for `i < d'`, `j ≥ ℓ'`, and
`dℓ' ≤ rank(M)(d' + ℓ')`. If `ℓ' < ℓ`, the entry `(PMQ)_{0,ℓ−1}` vanishes; it equals `Σᵢ Σⱼ τᵢ σⱼ Mᵢⱼ` for
`τ` the first row of `P` and `σ` the last column of `Q`, both algebraic and non-zero because `P` and `Q` are
invertible (a zero row or column would make the determinant vanish). This contradicts the hypothesis, so
`ℓ' = ℓ` and `dℓ ≤ rank(M)(d' + ℓ) ≤ rank(M)(d + ℓ)`. -/

namespace RC3_C21
open DiazModulus

/-- The entry `(PMQ)ᵢⱼ` as a double sum `Σₐ Σ_b P_{ia} Q_{bj} M_{ab}`. -/
theorem pmq_apply {d l : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (M : Matrix (Fin d) (Fin l) ℂ)
    (Q : Matrix (Fin l) (Fin l) ℂ) (i : Fin d) (j : Fin l) :
    (P * M * Q) i j = ∑ a, ∑ b, P i a * Q b j * M a b := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end RC3_C21

open DiazModulus RC3_C21 in
theorem solution {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hfree : ∀ (τ : Fin d → ℂ) (σ : Fin l → ℂ), (∀ i, τ i ∈ Qbar) → (∀ j, σ j ∈ Qbar) →
      τ ≠ 0 → σ ≠ 0 → ∑ i, ∑ j, τ i * σ j * M i j ≠ 0) :
    d * l ≤ M.rank * (d + l) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  obtain ⟨d', l', P, Q, hd'0, hd'd, hl'l, hP, hQ, hPa, hQa, hz, hineq⟩ :=
    DiazModulus.roy_rank_bound M hM hd
  have hl' : l' = l := by
    by_contra hne
    have hlt : l' < l := lt_of_le_of_ne hl'l hne
    let i₀ : Fin d := ⟨0, hd⟩
    let j₀ : Fin l := ⟨l - 1, by omega⟩
    have h0 : (P * M * Q) i₀ j₀ = 0 := hz i₀ j₀ hd'0 (by simp [j₀]; omega)
    rw [pmq_apply] at h0
    refine hfree (fun a => P i₀ a) (fun b => Q b j₀) (fun a => hPa _ _) (fun b => hQa _ _) ?_ ?_ h0
    · intro h
      exact hP.ne_zero (Matrix.det_eq_zero_of_row_eq_zero i₀ fun a => congrFun h a)
    · intro h
      exact hQ.ne_zero (Matrix.det_eq_zero_of_column_eq_zero j₀ fun b => congrFun h b)
  subst hl'
  calc d * l' ≤ M.rank * (d' + l') := hineq
    _ ≤ M.rank * (d + l') := Nat.mul_le_mul_left _ (by omega)
