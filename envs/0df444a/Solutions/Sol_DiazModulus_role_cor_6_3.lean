-- Prove2me | solution 1 for DiazModulus.role_cor_6_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:34:54.703197+00:00
-- url     : https://prove2.me/submissions/6ba9fa8e-df21-4daf-bf22-c4097981f175

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_variations_theorem_2_11

open Complex ComplexConjugate

/-! # Waldschmidt, *Role* Cor. 6.3 (*Variations* Cor. 2.12 with the corrected hypothesis)

Apply *Variations* Th. 2.11 with `m = 2`, `ℓ = 5`, `Λ₁ = −Λ₂₁` and `Λ₂ = Λ₁₁`. Both lie in `ℒ̃`, a `Q̄`-subspace.
`1, Λ₁, Λ₂` are `Q̄`-free: a relation `a + bΛ₁ + cΛ₂ = 0` reads `a + cΛ₁₁ + (−b)Λ₂₁ = 0`, so `a = b = c = 0` by the
freeness of `1, Λ₁₁, Λ₂₁`. The columns of `(I₂, M)` are `Q̄`-free by hypothesis and `5 > 2²`. So some
`Λ₁Λ₁ⱼ + Λ₂Λ₂ⱼ = Λ₁₁Λ₂ⱼ − Λ₂₁Λ₁ⱼ` is not in `ℒ̃`; for the first column this number is
`Λ₁₁Λ₂₁ − Λ₂₁Λ₁₁ = 0 ∈ ℒ̃`, so the column is one of the last four. -/

namespace RC2_C63
open DiazModulus

theorem lam_mem (M : Matrix (Fin 2) (Fin 5) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde) :
    ∀ i, (![-M 1 0, M 0 0] : Fin 2 → ℂ) i ∈ LogAlgTilde := by
  intro i; fin_cases i
  · simpa using (LogAlgTilde).neg_mem (hM 1 0)
  · simpa using hM 0 0

theorem lam_ind (M : Matrix (Fin 2) (Fin 5) ℂ) (h1 : LinearIndependent (↥Qbar) ![1, M 0 0, M 1 0]) :
    LinearIndependent (↥Qbar) (Fin.cons 1 ![-M 1 0, M 0 0] : Fin (2 + 1) → ℂ) := by
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro g hg
  have key := h1 ![g 0, g 2, -g 1] (by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Subfield.smul_def] at hg ⊢
    simp at hg ⊢
    linear_combination hg)
  intro i
  fin_cases i
  · simpa using key 0
  · simpa using key 2
  · simpa using key 1

end RC2_C63

open DiazModulus RC2_C63 in
theorem solution (M : Matrix (Fin 2) (Fin 5) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (h1 : LinearIndependent (↥Qbar) ![1, M 0 0, M 1 0])
    (hcol : LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col) :
    ∃ j : Fin 5, j ≠ 0 ∧ M 0 0 * M 1 j - M 1 0 * M 0 j ∉ LogAlgTilde := by
  obtain ⟨j, hj⟩ := DiazModulus.variations_theorem_2_11 M hM hcol ![-M 1 0, M 0 0] (lam_mem M hM)
    (lam_ind M h1) (by norm_num)
  have hsum : ∑ i, (![-M 1 0, M 0 0] : Fin 2 → ℂ) i * M i j = M 0 0 * M 1 j - M 1 0 * M 0 j := by
    simp [Fin.sum_univ_two]; ring
  refine ⟨j, ?_, hsum ▸ hj⟩
  rintro rfl
  apply hj
  rw [hsum, show M 0 0 * M 1 0 - M 1 0 * M 0 0 = 0 by ring]
  exact LogAlgTilde.zero_mem
