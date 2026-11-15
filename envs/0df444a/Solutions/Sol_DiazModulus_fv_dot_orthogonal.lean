-- Prove2me | solution 1 for DiazModulus.fv_dot_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:42:54.015019+00:00
-- url     : https://prove2.me/submissions/17295054-9b8d-4348-9492-86d21b29b19b

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The orthogonal of a subspace for the dot product

The dot product identifies `ℂⁿ` with its dual: `v ↦ (z ↦ v · z)` is a linear isomorphism. Let `Φ` be
the image of `W` under it, a subspace of the dual of dimension `dim W`. The orthogonal
`W^⊥ = {z : w · z = 0 for all w ∈ W}` is exactly the set of vectors on which every functional in `Φ`
vanishes, and the dimension of that common kernel is `n − dim Φ`. Hence
`dim W^⊥ + dim W = n`. -/

namespace RC3_DO
open DiazModulus
end RC3_DO

open DiazModulus RC3_DO in
theorem solution {n : ℕ} (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ V : Submodule ℂ (Fin n → ℂ), (∀ z, z ∈ V ↔ ∀ w ∈ W, w ⬝ᵥ z = 0) ∧
      Module.finrank ℂ ↥V + Module.finrank ℂ ↥W = n := by
  let e := dotProductEquiv ℂ (Fin n)
  let Φ : Submodule ℂ (Module.Dual ℂ (Fin n → ℂ)) := W.map (e : (Fin n → ℂ) →ₗ[ℂ] _)
  refine ⟨Φ.dualCoannihilator, fun z => ?_, ?_⟩
  · rw [Submodule.mem_dualCoannihilator]
    constructor
    · intro h w hw
      exact h (e w) (Submodule.mem_map_of_mem hw)
    · rintro h φ ⟨w, hw, rfl⟩
      exact h w hw
  · have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
    have h2 : Module.finrank ℂ ↥Φ = Module.finrank ℂ ↥W := LinearEquiv.finrank_map_eq e W
    rw [Module.finrank_fin_fun] at h1
    omega
