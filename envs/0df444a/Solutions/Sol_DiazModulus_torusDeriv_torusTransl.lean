-- Prove2me | solution 1 for DiazModulus.torusDeriv_torusTransl
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:03:55.816326+00:00
-- url     : https://prove2.me/submissions/6066dbfa-ef4a-4258-b6e1-60162ceafc93

import Mathlib
import Definitions.Def_DiazMultiplicity

open Complex ComplexConjugate

/-! # The invariant derivations commute with translations

Induction on `f` (`MvPolynomial.induction_on`). Both sides vanish on constants (`torusTransl g` is a `K`-algebra map
and `D_w` kills constants) and are additive. For `f = p · X_v`, the Leibniz rule for `D_w`, multiplicativity of
`σ_g = torusTransl g` and the induction hypothesis reduce the claim to the variables: `D_w (σ_g X_v) = σ_g (D_w X_v)`.
For `X_h` this is `D_w (X_h + x_h) = ξ_h = σ_g ξ_h`; for `Y_i` it is `D_w (y_i Y_i) = y_i η_i Y_i = σ_g (η_i Y_i)`,
and for `Z_i` the same with `y_i⁻¹` and `−η_i`. This is the invariance `D_w ∘ σ_g = σ_g ∘ D_w` of DALAG (8.10). -/

namespace C13_O2
open DiazModulus MvPolynomial

theorem torusDeriv_torusTransl_X {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K))
    (g : TorusGroup K A₀ A₁) (v : A₀ ⊕ (A₁ × Bool)) :
    torusDeriv w (torusTransl g (X v)) = torusTransl g (torusDeriv w (X v)) := by
  rcases v with h | ⟨i, b⟩
  · simp [torusTransl, MvPolynomial.derivation_C]
  · cases b <;>
    · simp only [torusTransl, aeval_X, Sum.elim_inr, torusDeriv_X_inr, Bool.false_eq_true, if_false,
        if_true, map_neg, map_mul, Derivation.leibniz, MvPolynomial.derivation_C,
        smul_eq_mul, aeval_C, algebraMap_eq]
      ring

end C13_O2

open DiazModulus C13_O2 in
theorem solution {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K)) (g : TorusGroup K A₀ A₁)
    (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :
    torusDeriv w (torusTransl g f) = torusTransl g (torusDeriv w f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [torusTransl, MvPolynomial.derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, hp, torusDeriv_torusTransl_X]
