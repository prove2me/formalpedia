-- Prove2me | solution 2 for Diaz.conj_not_linear_of_I
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:21:00.602349+00:00
-- url     : https://prove2.me/submissions/4c702be0-f283-4f5a-8448-e2acd5ccd735

/-
`Diaz.conj_not_linear_of_I` is `Diaz.conj_not_linear_hull` at `a = i`: a map
that were `ℂ`-linear on all of `ℂ` would in particular be linear on any hull,
and `conj i ≠ i`.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Theorems.Thm_Diaz_conj_not_linear_hull

namespace Diaz

end Diaz

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

open Diaz in
theorem solution :
    ¬ (∀ z : ℂ, conj (Complex.I * z) = Complex.I * conj z) := by
  intro h
  refine Diaz.conj_not_linear_hull (K := (⊥ : Subfield ℂ)) (u := (0 : ℂ))
    (a := Complex.I) ?_ (fun z _ => h z)
  rw [Complex.conj_I]
  intro hc
  exact Complex.I_ne_zero (by linear_combination -hc / 2)
end
