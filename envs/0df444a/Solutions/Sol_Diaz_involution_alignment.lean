-- Prove2me | solution 1 for Diaz.involution_alignment
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:17:07.023424+00:00
-- url     : https://prove2.me/submissions/1e3d21ed-979b-4f9a-8345-3d70433a40a0

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {R : Type*} [Field R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    {u c : R} (hu : u ≠ 0) (hc : σ c = c) (h : σ u = c * u) :
    c = 1 ∨ c = -1 := by
  have h2 : u = c * (c * u) := by
    conv_lhs => rw [← hσ u]
    rw [h, map_mul, hc, h]
  have hc2 : (c - 1) * (c + 1) * u = 0 := by linear_combination -h2
  rcases mul_eq_zero.1 hc2 with h3 | h3
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · left; linear_combination h4
    · right; linear_combination h4
  · exact absurd h3 hu
