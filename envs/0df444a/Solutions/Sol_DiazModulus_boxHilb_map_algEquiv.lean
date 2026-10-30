-- Prove2me | solution 1 for DiazModulus.boxHilb_map_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:09:23.978318+00:00
-- url     : https://prove2.me/submissions/d4fbb033-39a2-499f-9b4f-25457e11c3ec

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # The box Hilbert function under a filtration-preserving automorphism

If `σ ∈ Aut_K(S)` maps `F_T` onto itself, then `h_{σ(I)}(T) = h_I(T)`.

Let `q_I : S → S ⧸ I` and `q_{σI} : S → S ⧸ σ(I)` be the quotient maps, and let
`φ : S ⧸ I ≃ S ⧸ σ(I)` be the `K`-algebra isomorphism induced by `σ`
(`Ideal.quotientEquivAlg`), so that `φ ∘ q_I = q_{σI} ∘ σ`. Since `σ(F_T) = F_T`,
`q_{σI}(F_T) = q_{σI}(σ(F_T)) = φ(q_I(F_T))` (`Submodule.map_comp`), and a linear isomorphism
preserves the dimension of a subspace (`LinearEquiv.finrank_map_eq`). -/

namespace C11_F5
open DiazModulus
end C11_F5

open DiazModulus C11_F5 in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (σ : S ≃ₐ[K] S) (I : Ideal S) (T : B → ℕ)
    (hσ : (F T).map σ.toLinearMap = F T) :
    boxHilb F (I.map σ) T = boxHilb F I T := by
  unfold boxHilb
  let φ : (S ⧸ I) ≃ₐ[K] (S ⧸ I.map σ) := Ideal.quotientEquivAlg I (I.map σ) σ rfl
  have hcomp : (Ideal.Quotient.mkₐ K (I.map σ)).toLinearMap ∘ₗ σ.toLinearMap =
      φ.toLinearEquiv.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    rfl
  conv_lhs => rw [← hσ, ← Submodule.map_comp, hcomp, Submodule.map_comp]
  exact LinearEquiv.finrank_map_eq φ.toLinearEquiv _
