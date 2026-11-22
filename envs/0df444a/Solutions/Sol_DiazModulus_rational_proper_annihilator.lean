-- Prove2me | solution 1 for DiazModulus.rational_proper_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T09:04:19.156066+00:00
-- url     : https://prove2.me/submissions/4ba53eaa-f8e0-47f5-a702-6cfe00a69969

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_rational_common_kernel

open Complex ComplexConjugate

/-! # A proper rational subspace is killed by a non-zero algebraic linear form

Let `T ⊊ ℂᵈ` be spanned by its algebraic vectors. Such a subspace is the common kernel of `d` linear forms
`ψ₁, …, ψ_d` with algebraic coefficients: `v ∈ T` exactly when `ψᵢ · v = 0` for every `i`. If every `ψᵢ` were
the zero form, every vector of `ℂᵈ` would satisfy these equations, so `T` would be all of `ℂᵈ`, against the
hypothesis. Hence some `ψᵢ` is non-zero; it has algebraic coefficients and vanishes on `T`, so `φ = ψᵢ` is the
required form. -/

open DiazModulus in
theorem solution {d : ℕ} (T : Submodule ℂ (Fin d → ℂ))
    (hT : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T) (hTop : T ≠ ⊤) :
    ∃ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) ∧ φ ≠ 0 ∧ ∀ v ∈ T, φ ⬝ᵥ v = 0 := by
  obtain ⟨ψ, hψQ, hψT⟩ := DiazModulus.rational_common_kernel T hT
  have hne : ∃ i, ψ i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hTop
    rw [eq_top_iff]
    intro v _
    rw [hψT v]
    intro i
    simp [h i]
  obtain ⟨i, hi⟩ := hne
  exact ⟨ψ i, hψQ i, hi, fun v hv => (hψT v).1 hv i⟩
