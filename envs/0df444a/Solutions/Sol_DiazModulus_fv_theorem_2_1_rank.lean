-- Prove2me | solution 1 for DiazModulus.fv_theorem_2_1_rank
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:08:11.41284+00:00
-- url     : https://prove2.me/submissions/f41bb988-fea8-4db9-80fa-423267de03aa

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fv_rank_quot_witness
import Theorems.Thm_DiazModulus_fv_theorem_2_1_general

open Complex ComplexConjugate

/-! # Waldschmidt's Theorem 2.1 with the hypothesis on dim Y/(Y ∩ V) as a cardinal

Write `d = dim X`, `c(V) = n − dim V` and `κ(V) = dim_Q̄ Y/(Y ∩ V)`, a cardinal. We reduce to the form of
the theorem whose hypothesis asks, for each `V ≠ ℂⁿ`, for a finite-dimensional `Y₀ ⊆ Y` with
`d·c(V) < (d − n)·(dim Y₀ − dim (Y₀ ∩ V))`. Fix `V ≠ ℂⁿ`. If `κ(V)` is a natural number `k`, the cardinal
inequality `d·c(V) < (d − n)·k` is an inequality of natural numbers, and the witness lemma (from `k`
independent classes of `Y/(Y ∩ V)`) gives `Y₀` with `dim Y₀ − dim (Y₀ ∩ V) ≥ k`. If `κ(V)` is infinite, the
witness lemma with `N = d·c(V) + 1` gives `Y₀` with `dim Y₀ − dim (Y₀ ∩ V) ≥ d·c(V) + 1`, and
`d − n ≥ 1` gives `(d − n)·(d·c(V) + 1) > d·c(V)`. -/

open DiazModulus in
theorem solution {n : ℕ} (X Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X]
    (hdn : n < Module.finrank (↥Qbar) ↥X)
    (hμ : ∀ V : Submodule ℂ (Fin n → ℂ), V ≠ ⊤ →
      ((Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V) : ℕ) : Cardinal) <
        ((Module.finrank (↥Qbar) ↥X - n : ℕ) : Cardinal) *
          Module.rank (↥Qbar) (↥Y ⧸ (V.restrictScalars (↥Qbar)).comap Y.subtype)) :
    ∃ x ∈ X, ∃ y ∈ Y, x ⬝ᵥ y ∉ LogAlgTilde := by
  refine DiazModulus.fv_theorem_2_1_general X Y hdn ?_
  intro V hV
  have h := hμ V hV
  have he : 1 ≤ Module.finrank (↥Qbar) ↥X - n := by omega
  rcases lt_or_ge (Module.rank (↥Qbar) (↥Y ⧸ (V.restrictScalars (↥Qbar)).comap Y.subtype))
      Cardinal.aleph0 with hfin | hinf
  · obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 hfin
    rw [hk] at h
    have h' : Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V) <
        (Module.finrank (↥Qbar) ↥X - n) * k := by exact_mod_cast h
    obtain ⟨Y₀, hle, hfd, hN⟩ := DiazModulus.fv_rank_quot_witness Y V k hk.ge
    exact ⟨Y₀, hle, hfd, lt_of_lt_of_le h' (Nat.mul_le_mul_left _ hN)⟩
  · obtain ⟨Y₀, hle, hfd, hN⟩ := DiazModulus.fv_rank_quot_witness Y V
      (Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V) + 1)
      (Cardinal.natCast_lt_aleph0.le.trans hinf)
    refine ⟨Y₀, hle, hfd, ?_⟩
    calc Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V)
        < 1 * (Module.finrank (↥Qbar) ↥X * (n - Module.finrank ℂ ↥V) + 1) := by omega
      _ ≤ (Module.finrank (↥Qbar) ↥X - n) * _ := Nat.mul_le_mul he hN
