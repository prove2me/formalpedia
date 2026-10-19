-- Prove2me | solution 1 for DiazModulus.transcendental_add_mul_add_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T17:59:52.055366+00:00
-- url     : https://prove2.me/submissions/e40449fc-47ce-49bf-9a90-c34dae8f1e61

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # `a + b u + c ū` is transcendental over `F`

Let `u` be transcendental over a subfield `F` of `ℂ` with `ρ = u ū ∈ F`, and let `a, b, c ∈ F` with
`(b, c) ≠ (0, 0)`. Put `e = a + b u + c ū`. Since `u ≠ 0`, multiplying by `u` gives
`b u² + (a − e) u + c ρ = 0`. So `u` is a root of `b X² + (a − e) X + c ρ`, a polynomial over the
intermediate field `F(e)`; it is non-zero because its `X²` coefficient is `b` and its constant term is
`c ρ` with `ρ ≠ 0`. If `e` were algebraic over `F`, then `F(e)/F` would be algebraic
(`IntermediateField.isAlgebraic_adjoin_simple`), and `u`, algebraic over `F(e)`, would be algebraic
over `F` (`IsAlgebraic.restrictScalars`), a contradiction.
-/

namespace R19_F1

end R19_F1

open DiazModulus R19_F1 in
theorem solution
    (F : Subfield ℂ) (u : ℂ) (hu : Transcendental F u) (hρ : u * conj u ∈ F)
    (a b c : ℂ) (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hbc : b ≠ 0 ∨ c ≠ 0) :
    Transcendental F (a + b * u + c * conj u) := by
  intro he
  set e := a + b * u + c * conj u with he_def
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu isAlgebraic_zero
  have hρ0 : u * conj u ≠ 0 := mul_ne_zero hu0 ((map_ne_zero _).mpr hu0)
  let E : IntermediateField F ℂ := IntermediateField.adjoin F {e}
  have hE : Algebra.IsAlgebraic F E := IntermediateField.isAlgebraic_adjoin_simple he.isIntegral
  have hFE : ∀ x ∈ F, x ∈ E := fun x hx => E.algebraMap_mem ⟨x, hx⟩
  have heE : e ∈ E := IntermediateField.mem_adjoin_simple_self F e
  let p : Polynomial E :=
    Polynomial.C ⟨b, hFE b hb⟩ * Polynomial.X ^ 2 +
      Polynomial.C ⟨a - e, sub_mem (hFE a ha) heE⟩ * Polynomial.X +
      Polynomial.C ⟨c * (u * conj u), hFE _ (mul_mem hc hρ)⟩
  have hp0 : p ≠ 0 := by
    intro hp
    rcases hbc with hb0 | hc0
    · have := congrArg (fun q => q.coeff 2) hp
      simp [p] at this
      exact hb0 (by simpa using congrArg Subtype.val this)
    · have := congrArg (fun q => q.coeff 0) hp
      simp [p] at this
      exact mul_ne_zero hc0 hρ0 (by simpa using congrArg Subtype.val this)
  have hpu : Polynomial.aeval u p = 0 := by
    simp [p, he_def]
    ring
  have huE : IsAlgebraic E u := ⟨p, hp0, hpu⟩
  exact hu (huE.restrictScalars F)
