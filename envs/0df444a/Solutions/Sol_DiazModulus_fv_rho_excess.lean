-- Prove2me | solution 1 for DiazModulus.fv_rho_excess
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:16:22.864234+00:00
-- url     : https://prove2.me/submissions/17a9b48d-93f9-4fd2-a5d1-3cb7704454a7

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The excess of a larger Q̄-subspace does not grow with the ℂ-subspace

For `Q̄`-subspaces `Y ⊆ Y'` (with `Y'` finite-dimensional) and a `ℂ`-subspace `W` write
`ρ_Z(W) = dim Z − dim (Z ∩ W)`. Since `Y ⊆ Y'`, `Y ∩ (Y' ∩ W) = Y ∩ W`, so Grassmann's formula for `Y` and
`Y' ∩ W` reads `dim (Y + (Y' ∩ W)) + dim (Y ∩ W) = dim Y + dim (Y' ∩ W)`. Hence the excess
`ρ_{Y'}(W) − ρ_Y(W)` equals `dim Y' − dim (Y + (Y' ∩ W))`. For `V ⊆ V'` the space `Y + (Y' ∩ V)` lies in
`Y + (Y' ∩ V')`, which lies in `Y'`, so the excess at `V'` is at most the excess at `V`. Written additively
this is `ρ_{Y'}(V') + ρ_Y(V) ≤ ρ_Y(V') + ρ_{Y'}(V)`; every truncated subtraction is exact because each
intersection lies in its space. -/

open DiazModulus in
theorem solution {n : ℕ} (Y Y' : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥Y'] (hYY' : Y ≤ Y')
    (V V' : Submodule ℂ (Fin n → ℂ)) (hVV' : V ≤ V') :
    (Module.finrank (↥Qbar) ↥Y' - Module.finrank (↥Qbar) ↥(Y' ⊓ V'.restrictScalars (↥Qbar))) +
        (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar))) ≤
      (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V'.restrictScalars (↥Qbar))) +
        (Module.finrank (↥Qbar) ↥Y' - Module.finrank (↥Qbar) ↥(Y' ⊓ V.restrictScalars (↥Qbar))) := by
  have fY : FiniteDimensional (↥Qbar) ↥Y := Submodule.finiteDimensional_of_le hYY'
  have key : ∀ W : Submodule ℂ (Fin n → ℂ),
      Module.finrank (↥Qbar) ↥(Y ⊔ (Y' ⊓ W.restrictScalars (↥Qbar))) +
        Module.finrank (↥Qbar) ↥(Y ⊓ W.restrictScalars (↥Qbar)) =
      Module.finrank (↥Qbar) ↥Y + Module.finrank (↥Qbar) ↥(Y' ⊓ W.restrictScalars (↥Qbar)) := by
    intro W
    have fW : FiniteDimensional (↥Qbar) ↥(Y' ⊓ W.restrictScalars (↥Qbar)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have h := Submodule.finrank_sup_add_finrank_inf_eq Y (Y' ⊓ W.restrictScalars (↥Qbar))
    have e : Y ⊓ (Y' ⊓ W.restrictScalars (↥Qbar)) = Y ⊓ W.restrictScalars (↥Qbar) := by
      rw [← inf_assoc, inf_of_le_left hYY']
    rw [e] at h; exact h
  have kV := key V
  have kV' := key V'
  have mono : Y ⊔ (Y' ⊓ V.restrictScalars (↥Qbar)) ≤ Y ⊔ (Y' ⊓ V'.restrictScalars (↥Qbar)) :=
    sup_le_sup_left (inf_le_inf_left _ (Submodule.restrictScalars_mono _ hVV')) _
  have m1 := Submodule.finrank_mono (t := Y') (sup_le hYY' inf_le_left :
    Y ⊔ (Y' ⊓ V'.restrictScalars (↥Qbar)) ≤ Y')
  have fS : FiniteDimensional (↥Qbar) ↥(Y ⊔ (Y' ⊓ V'.restrictScalars (↥Qbar))) :=
    Submodule.finiteDimensional_of_le (sup_le hYY' inf_le_left)
  have m2 := Submodule.finrank_mono mono
  have a1 := Submodule.finrank_mono (t := Y) (inf_le_left : Y ⊓ V.restrictScalars (↥Qbar) ≤ Y)
  have a2 := Submodule.finrank_mono (t := Y) (inf_le_left : Y ⊓ V'.restrictScalars (↥Qbar) ≤ Y)
  have a3 := Submodule.finrank_mono (t := Y') (inf_le_left : Y' ⊓ V.restrictScalars (↥Qbar) ≤ Y')
  have a4 := Submodule.finrank_mono (t := Y') (inf_le_left : Y' ⊓ V'.restrictScalars (↥Qbar) ≤ Y')
  omega
