-- Prove2me | solution 1 for DiazModulus.fv_rho_inf
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:18:38.275194+00:00
-- url     : https://prove2.me/submissions/eaf7bb91-b46e-4ab8-bb5d-7767d70dd50f

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Codimension of a Q̄-subspace in an intersection of two ℂ-subspaces

For a finite-dimensional `Q̄`-subspace `Y` and `ℂ`-subspaces `V₁, V₂` write `ρ(V) = dim Y − dim (Y ∩ V)`.
Put `A = Y ∩ V₁` and `B = Y ∩ V₂`. Restriction of scalars commutes with intersection, so
`Y ∩ (V₁ ∩ V₂) = A ∩ B`. Grassmann's formula gives `dim (A + B) + dim (A ∩ B) = dim A + dim B`, and
`A + B ⊆ Y` gives `dim (A + B) ≤ dim Y`. Hence `dim (A ∩ B) ≥ dim A + dim B − dim Y`, which is
`ρ(V₁ ∩ V₂) ≤ ρ(V₁) + ρ(V₂)`; the natural-number subtractions are exact because `A, B ⊆ Y`. -/

open DiazModulus in
theorem solution {n : ℕ} (Y : Submodule (↥Qbar) (Fin n → ℂ)) [FiniteDimensional (↥Qbar) ↥Y]
    (V₁ V₂ : Submodule ℂ (Fin n → ℂ)) :
    Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ (V₁ ⊓ V₂).restrictScalars (↥Qbar)) ≤
      (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V₁.restrictScalars (↥Qbar))) +
        (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V₂.restrictScalars (↥Qbar))) := by
  have hAB : Y ⊓ (V₁ ⊓ V₂).restrictScalars (↥Qbar) =
      (Y ⊓ V₁.restrictScalars (↥Qbar)) ⊓ (Y ⊓ V₂.restrictScalars (↥Qbar)) := by
    rw [Submodule.restrictScalars_inf, inf_inf_distrib_left]
  rw [hAB]
  have fA : FiniteDimensional (↥Qbar) ↥(Y ⊓ V₁.restrictScalars (↥Qbar)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have fB : FiniteDimensional (↥Qbar) ↥(Y ⊓ V₂.restrictScalars (↥Qbar)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hG := Submodule.finrank_sup_add_finrank_inf_eq (Y ⊓ V₁.restrictScalars (↥Qbar))
    (Y ⊓ V₂.restrictScalars (↥Qbar))
  have h1 := Submodule.finrank_mono (t := Y)
    (sup_le (inf_le_left : Y ⊓ V₁.restrictScalars (↥Qbar) ≤ Y)
      (inf_le_left : Y ⊓ V₂.restrictScalars (↥Qbar) ≤ Y))
  have h2 := Submodule.finrank_mono (t := Y) (inf_le_left : Y ⊓ V₁.restrictScalars (↥Qbar) ≤ Y)
  have h3 := Submodule.finrank_mono (t := Y) (inf_le_left : Y ⊓ V₂.restrictScalars (↥Qbar) ≤ Y)
  omega
