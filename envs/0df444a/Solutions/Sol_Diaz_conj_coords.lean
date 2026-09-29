-- Prove2me | solution 1 for Diaz.conj_coords
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:10.710314+00:00
-- url     : https://prove2.me/submissions/0c24401a-616e-4913-964f-6c10191ac076

import Mathlib


section
open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

theorem solution (t : ℂ) (a b : ℚ) :
    conj ((a : ℂ) * t + (b : ℂ) * conj t) = (b : ℂ) * t + (a : ℂ) * conj t := by
  simp only [map_add, map_mul, Complex.conj_conj, map_ratCast]
  ring
end
