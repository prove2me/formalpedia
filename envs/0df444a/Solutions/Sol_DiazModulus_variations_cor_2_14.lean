-- Prove2me | solution 1 for DiazModulus.variations_cor_2_14
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:32:34.885297+00:00
-- url     : https://prove2.me/submissions/ac975405-9fbd-4caf-83b3-d336d5a4acb8

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_baker_linear_forms_in_logarithms
import Theorems.Thm_DiazModulus_baker_columns_qbar_independent
import Theorems.Thm_DiazModulus_variations_theorem_2_11

open Complex ComplexConjugate

/-! # Waldschmidt's Corollary 2.14 of *Variations*

Let `M = (λ_{ij})` be an `m × ℓ` matrix with entries in `ℒ` and `ℚ`-free columns, let `λ₁, …, λ_m ∈ ℒ` be
`ℚ`-free, and let `ℓ > m²`. Baker's theorem in column form says that the `m + ℓ` columns of `(I_m, M)` are
`Q̄`-free. Baker's theorem itself says that `1, λ₁, …, λ_m` are `Q̄`-free: a relation
`b₀ + Σ bᵢλᵢ = 0` with algebraic coefficients not all zero is exactly what it excludes. Since `ℒ ⊆ ℒ̃`
(`ℒ` is among the generators of `ℒ̃`), the theorem on products of `ℒ̃`-matrices by `ℒ̃`-vectors
(*Variations* Th. 2.11) applies with `Λᵢ = λᵢ` and gives a column `j` with `Σᵢ λᵢλ_{ij} ∉ ℒ̃`. -/

namespace RC2_C214
open DiazModulus

theorem logAlg_subset_tilde {u : ℂ} (hu : u ∈ LogAlg) : u ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert_of_mem _ hu)

/-- Baker: `1, l₁, …, l_m` are `Q̄`-free when the `lᵢ ∈ ℒ` are `ℚ`-free. -/
theorem cons_one_qbar_independent {m : ℕ} (l : Fin m → ℂ) (hl : ∀ i, l i ∈ LogAlg)
    (hlind : LinearIndependent ℚ l) :
    LinearIndependent (↥Qbar) (Fin.cons 1 l : Fin (m + 1) → ℂ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨k, hk⟩ := hne
  apply Schanuel.baker_linear_forms_in_logarithms m l hlind hl (g 0 : ℂ) (fun i => (g (Fin.succ i) : ℂ))
    (mem_Qbar_iff.mp (g 0).2) (fun i => mem_Qbar_iff.mp (g (Fin.succ i)).2)
  · refine Fin.cases (fun h0 => Or.inl ?_) (fun i hi => Or.inr ⟨i, ?_⟩) k hk
    · exact_mod_cast h0
    · exact_mod_cast hi
  · rw [Fin.sum_univ_succ] at hg
    simpa [Subfield.smul_def] using hg

end RC2_C214

open DiazModulus RC2_C214 in
theorem solution {m ℓ : ℕ} (M : Matrix (Fin m) (Fin ℓ) ℂ) (hM : ∀ i j, M i j ∈ LogAlg)
    (hcol : LinearIndependent ℚ M.col) (l : Fin m → ℂ) (hl : ∀ i, l i ∈ LogAlg)
    (hlind : LinearIndependent ℚ l) (hℓ : m ^ 2 < ℓ) :
    ∃ j : Fin ℓ, ∑ i, l i * M i j ∉ LogAlgTilde := by
  exact DiazModulus.variations_theorem_2_11 M (fun i j => logAlg_subset_tilde (hM i j))
    (DiazModulus.baker_columns_qbar_independent M hM hcol) l (fun i => logAlg_subset_tilde (hl i))
    (cons_one_qbar_independent l hl hlind) hℓ
