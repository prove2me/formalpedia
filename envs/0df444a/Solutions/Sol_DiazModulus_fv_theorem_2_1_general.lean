-- Prove2me | solution 1 for DiazModulus.fv_theorem_2_1_general
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:10:27.544882+00:00
-- url     : https://prove2.me/submissions/d2bc170a-2d98-4a17-b3ca-34c3f1a16467

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fv_theorem_2_1
import Theorems.Thm_DiazModulus_fv_finite_approx

open Complex ComplexConjugate

/-! # Waldschmidt's Theorem 2.1 for an arbitrary Q̄-subspace Y

Write `d = dim X`, `ρ_Z(V) = dim Z − dim (Z ∩ V)` and `c(V) = n − dim V`. The finite-approximation
theorem with the cap `B = d·n + 1` gives one finite-dimensional `Y₀ ⊆ Y` with
`ρ_{Y₀}(V) ≥ min (ρ_{Y₁}(V), B)` for every `ℂ`-subspace `V` and every finite-dimensional `Y₁ ⊆ Y`. We check
the hypothesis of the finite-dimensional theorem for `(X, Y₀)`. Fix `V ≠ ℂⁿ` and take the witness `Y₁`
of the hypothesis, so `d·c(V) < (d − n)·ρ_{Y₁}(V)`. If `ρ_{Y₁}(V) ≤ B` then `ρ_{Y₀}(V) ≥ ρ_{Y₁}(V)` and the
inequality passes to `Y₀`. Otherwise `ρ_{Y₀}(V) ≥ B = d·n + 1`, and since `d − n ≥ 1` and `c(V) ≤ n`,
`(d − n)·ρ_{Y₀}(V) ≥ d·n + 1 > d·c(V)`. The finite-dimensional theorem then gives `x ∈ X` and `y ∈ Y₀ ⊆ Y`
with `x·y ∉ ℒ̃`. -/

open DiazModulus in
theorem solution {n : ℕ} (X Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X]
    (hdn : n < Module.finrank (↥Qbar) ↥X)
    (hμ : ∀ V : Submodule ℂ (Fin n → ℂ), V ≠ ⊤ →
      ∃ Y₀ : Submodule (↥Qbar) (Fin n → ℂ), Y₀ ≤ Y ∧ FiniteDimensional (↥Qbar) ↥Y₀ ∧
        Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V) <
          (Module.finrank (↥Qbar) ↥X - n) *
            (Module.finrank (↥Qbar) ↥Y₀ -
              Module.finrank (↥Qbar) ↥(Y₀ ⊓ V.restrictScalars (↥Qbar)))) :
    ∃ x ∈ X, ∃ y ∈ Y, x ⬝ᵥ y ∉ LogAlgTilde := by
  obtain ⟨Y₀, hY₀Y, hfd, happ⟩ :=
    DiazModulus.fv_finite_approx Y (Module.finrank (↥Qbar) ↥X * n + 1)
  have := hfd
  obtain ⟨x, hx, y, hy, h⟩ := DiazModulus.fv_theorem_2_1 X Y₀ hdn (by
    intro V hV
    obtain ⟨Y₁, hY₁Y, hfd₁, hlt⟩ := hμ V hV
    have h1 := happ V Y₁ hY₁Y hfd₁
    generalize Module.finrank (↥Qbar) ↥X = d at *
    generalize hr₁ : Module.finrank (↥Qbar) ↥Y₁ -
      Module.finrank (↥Qbar) ↥(Y₁ ⊓ V.restrictScalars (↥Qbar)) = r₁ at *
    generalize hr₀ : Module.finrank (↥Qbar) ↥Y₀ -
      Module.finrank (↥Qbar) ↥(Y₀ ⊓ V.restrictScalars (↥Qbar)) = r₀ at *
    have hc : n - Module.finrank ℂ ↥V ≤ n := Nat.sub_le _ _
    generalize n - Module.finrank ℂ ↥V = c at *
    have he : 1 ≤ d - n := by omega
    rcases le_total r₁ (d * n + 1) with h | h
    · rw [min_eq_left h] at h1
      exact lt_of_lt_of_le hlt (Nat.mul_le_mul_left _ h1)
    · rw [min_eq_right h] at h1
      calc d * c ≤ d * n := Nat.mul_le_mul_left _ hc
        _ < 1 * (d * n + 1) := by omega
        _ ≤ (d - n) * r₀ := Nat.mul_le_mul he h1)
  exact ⟨x, hx, y, hY₀Y hy, h⟩
