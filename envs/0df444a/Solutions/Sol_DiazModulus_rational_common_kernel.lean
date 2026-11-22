-- Prove2me | solution 1 for DiazModulus.rational_common_kernel
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T09:06:40.265681+00:00
-- url     : https://prove2.me/submissions/b2ae4ed8-1260-43bc-8f0b-b7e4dfe46cac

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rational_adapted_basis

open Complex ComplexConjugate

/-! # A rational subspace is the common kernel of algebraic linear forms

Let `T ⊂ ℂᵈ` be spanned by its algebraic vectors and put `r = dim T`. The adapted-basis theorem for rational
subspaces gives a linear automorphism `g` of `ℂᵈ` that maps algebraic vectors to algebraic vectors and such that
`v ∈ T` exactly when the coordinates `(g v)ᵢ` vanish for every `i ≥ r`. Let `M` be the matrix of `g` in the
standard basis: its `j`-th column is `g(eⱼ)`, an algebraic vector, so every entry of `M` is algebraic, and
`(g v)ᵢ = Mᵢ · v` for every `v`. Take `ψᵢ = 0` for `i < r` and `ψᵢ = Mᵢ`, the `i`-th row of `M`, for `i ≥ r`.
These `d` forms have algebraic coefficients, `ψᵢ · v = 0` holds trivially for `i < r` and says `(g v)ᵢ = 0` for
`i ≥ r`, so `v ∈ T` exactly when every `ψᵢ` vanishes at `v`. -/

namespace RC10_RatKer
open DiazModulus

/-- The standard basis vector `eⱼ` has algebraic entries. -/
theorem rc10_ratker_single_alg {d : ℕ} (j : Fin d) :
    ∀ i, (Pi.single j (1 : ℂ) : Fin d → ℂ) i ∈ Qbar := by
  intro i
  rw [Pi.single_apply]
  split_ifs
  · exact Qbar.one_mem
  · exact Qbar.zero_mem

end RC10_RatKer

open DiazModulus RC10_RatKer in
theorem solution {d : ℕ} (T : Submodule ℂ (Fin d → ℂ))
    (hT : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T) :
    ∃ ψ : Fin d → Fin d → ℂ, (∀ i j, ψ i j ∈ Qbar) ∧
      ∀ v : Fin d → ℂ, v ∈ T ↔ ∀ i, ψ i ⬝ᵥ v = 0 := by
  obtain ⟨g, hgQ, -, hgT⟩ := DiazModulus.roy_rational_adapted_basis T hT
  set r := Module.finrank ℂ ↥T
  have hMv : ∀ v : Fin d → ℂ, ∀ i, (fun j => g (Pi.single j 1) i) ⬝ᵥ v = g v i := by
    intro v i
    have := congrFun (LinearMap.toMatrix'_mulVec (g : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) v) i
    simpa [Matrix.mulVec] using this
  refine ⟨fun i => if r ≤ i.val then (fun j => g (Pi.single j 1) i) else 0, ?_, ?_⟩
  · intro i j
    dsimp only
    split_ifs
    · exact (hgQ _ (rc10_ratker_single_alg j)).1 i
    · exact Qbar.zero_mem
  · intro v
    rw [hgT v]
    refine forall_congr' fun i => ?_
    by_cases hi : r ≤ i.val
    · simp only [hi, if_true, hMv, forall_const]
    · simp only [hi, if_false, zero_dotProduct, IsEmpty.forall_iff]
