-- Prove2me | solution 1 for Diaz.conj_not_linear_of_I
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:12.055719+00:00
-- url     : https://prove2.me/submissions/8b8607a2-6aee-46bd-b925-dad4e174ed06

import Mathlib

namespace Diaz

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

/-- Conjugation is **not** `K`-linear once `K` contains a non-real number.

A `K`-linear map `f` would satisfy `f (a * z) = a * f z` for `a ∈ K`;
taking `z = 1` forces `conj a = a`, so only a totally real base field
could carry conjugation as a linear map.  Since the intended base is the
algebraic numbers, which contain `i`, conjugation on the hull is a ring
involution and nothing stronger. -/
theorem conj_not_linear {a : ℂ} (ha : conj a ≠ a) :
    ¬ (∀ z : ℂ, conj (a * z) = a * conj z) := by
  intro h
  exact ha (by simpa using h 1)
end

end Diaz

section
open ComplexConjugate
variable (K : Subfield ℂ) (u : ℂ)
variable {K u}

open Diaz in
theorem solution :
    ¬ (∀ z : ℂ, conj (Complex.I * z) = Complex.I * conj z) := by
  apply conj_not_linear
  intro h
  rw [Complex.conj_I] at h
  exact Complex.I_ne_zero (by linear_combination -h / 2)
end
