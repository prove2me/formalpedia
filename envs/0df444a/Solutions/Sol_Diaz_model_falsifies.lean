-- Prove2me | solution 1 for Diaz.model_falsifies
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:27:27.070848+00:00
-- url     : https://prove2.me/submissions/f98d77d7-73c4-4933-910d-fcdd7b8dd70f

import Mathlib
import Definitions.Def_Diaz_Exponential
import Theorems.Thm_Diaz_isAlgebraic_two_rpow

namespace Diaz

section
open ComplexConjugate

/-- Every value of `Exp₀` is algebraic: the model really is a model of
the *arithmetic* situation, not merely of the field structure. -/
theorem Exp0_isAlgebraic (x : ℚ × ℚ) : IsAlgebraic ℚ (Exp0 x) :=
  isAlgebraic_two_rpow _
end

end Diaz

section
open ComplexConjugate

open Diaz in
theorem solution {K : Subfield ℂ} {t : ℂ}
    (hρ : t * conj t ∈ K) (ht0 : t ≠ 0) :
    ∃ a b : ℚ, ((a : ℂ) * t + (b : ℂ) * conj t) ≠ 0
      ∧ IsAlgebraic ℚ (Exp0 (a, b))
      ∧ ((a : ℂ) * t + (b : ℂ) * conj t)
          * conj ((a : ℂ) * t + (b : ℂ) * conj t) ∈ K :=
  ⟨1, 0, by simpa using ht0, Exp0_isAlgebraic _, by simpa using hρ⟩
end
