-- Prove2me | solution 1 for Diaz.transcendental_of_candidate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:17.145724+00:00
-- url     : https://prove2.me/submissions/48bbfeb2-710d-4001-b8aa-ce6bd2cbf008

import Mathlib
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

theorem solution (hu : u ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) : Transcendental ℚ u :=
  fun halg => DiazModulus.hermite_lindemann_holds u hu halg hexp
end
