-- Prove2me | solution 1 for DiazModulus.isAlgebraic_of_mem_of_isAlgebraic_adjoin_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T17:59:49.346662+00:00
-- url     : https://prove2.me/submissions/bc768a85-5bc1-433d-986c-a4cfc48ba5f5

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # An element of `F` algebraic over `ℚ(w)`, with `w` transcendental over `F`, is algebraic

Let `w` be transcendental over a subfield `F` of `ℂ`, and let `z ∈ F` be algebraic over `ℚ(w)`.
Suppose `z` were transcendental over `ℚ`. Since `ℚ[z] ⊆ F`, the number `w` is transcendental over
`ℚ[z]` (a polynomial relation over `ℚ[z]` is one over `F`). By `AlgebraicIndependent.option_iff`
the family `(w, z)` is then algebraically independent over `ℚ`, and so is the swapped family
`(z, w)` (`AlgebraicIndependent.comp` with a permutation of `Option Unit`). Reading
`AlgebraicIndependent.option_iff` backwards for `(z, w)` makes `z` transcendental over `ℚ[w]`,
hence over `ℚ(w)` (`IntermediateField.transcendental_adjoin_iff`), a contradiction.
-/

namespace R19_F2

/-- `ℚ[z] ⊆ F` for `z ∈ F`. -/
theorem adjoin_le_subfield (F : Subfield ℂ) {z : ℂ} (hz : z ∈ F) :
    ∀ x ∈ Algebra.adjoin ℚ ({z} : Set ℂ), x ∈ F := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hz
  | algebraMap q => simp
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- If `w` is transcendental over `F` and `z ∈ F`, then `w` is transcendental over `ℚ[z]`. -/
theorem transcendental_adjoin_of_mem (F : Subfield ℂ) {w z : ℂ} (hw : Transcendental F w)
    (hz : z ∈ F) : Transcendental (Algebra.adjoin ℚ ({z} : Set ℂ)) w := by
  intro h
  set A := Algebra.adjoin ℚ ({z} : Set ℂ)
  have hAF := adjoin_le_subfield F hz
  let φ : A →+* F :=
    { toFun := fun x => ⟨x.1, hAF x.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra A F := φ.toAlgebra
  have : IsScalarTower A F ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap A F) := by
    intro x y hxy
    have h' := congrArg Subtype.val hxy
    exact Subtype.ext h'
  exact hw (h.extendScalars hinj)

end R19_F2

open DiazModulus R19_F2 in
theorem solution
    (F : Subfield ℂ) (w z : ℂ) (hw : Transcendental F w) (hz : z ∈ F)
    (h : IsAlgebraic (IntermediateField.adjoin ℚ ({w} : Set ℂ)) z) :
    IsAlgebraic ℚ z := by
  by_contra hzt
  have h1 : Transcendental (Algebra.adjoin ℚ (Set.range fun _ : Unit => z)) w := by
    rw [Set.range_const]
    exact transcendental_adjoin_of_mem F hw hz
  have hzw : AlgebraicIndependent ℚ (fun o : Option Unit => o.elim w fun _ => z) :=
    AlgebraicIndependent.option_iff.mpr ⟨algebraicIndependent_unique_type_iff.mpr hzt, h1⟩
  have hwz : AlgebraicIndependent ℚ (fun o : Option Unit => o.elim z fun _ => w) := by
    have := hzw.comp (Equiv.swap none (some ())) (Equiv.swap none (some ())).injective
    convert this using 1
    funext o
    rcases o with _ | _ <;> simp
  have h2 := (AlgebraicIndependent.option_iff.mp hwz).2
  rw [Set.range_const] at h2
  exact (IntermediateField.transcendental_adjoin_iff.mpr h2) h
