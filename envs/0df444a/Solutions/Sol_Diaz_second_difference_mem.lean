-- Prove2me | solution 1 for Diaz.second_difference_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:19:49.090703+00:00
-- url     : https://prove2.me/submissions/87d22de2-2a21-4fd7-95c5-146c93e30a3f

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {K : Subfield ℂ} {c d ρ : ℂ} {n₁ n₂ n₃ : ℤ}
    (h12 : n₁ ≠ n₂) (h13 : n₁ ≠ n₃) (h23 : n₂ ≠ n₃)
    (h1 : ρ + c * n₁ + d * n₁ ^ 2 ∈ K)
    (h2 : ρ + c * n₂ + d * n₂ ^ 2 ∈ K)
    (h3 : ρ + c * n₃ + d * n₃ ^ 2 ∈ K) : d ∈ K := by
  have e12 : ((n₂ : ℂ) - n₁) ≠ 0 := by
    simpa [sub_eq_zero, Int.cast_injective.eq_iff] using fun h => h12 h.symm
  have e13 : ((n₃ : ℂ) - n₁) ≠ 0 := by
    simpa [sub_eq_zero, Int.cast_injective.eq_iff] using fun h => h13 h.symm
  have e23 : ((n₃ : ℂ) - n₂) ≠ 0 := by
    simpa [sub_eq_zero, Int.cast_injective.eq_iff] using fun h => h23 h.symm
  have key : d = (((ρ + c * n₃ + d * n₃ ^ 2) - (ρ + c * n₁ + d * n₁ ^ 2)) / ((n₃ : ℂ) - n₁)
      - ((ρ + c * n₂ + d * n₂ ^ 2) - (ρ + c * n₁ + d * n₁ ^ 2)) / ((n₂ : ℂ) - n₁))
      / ((n₃ : ℂ) - n₂) := by
    field_simp
    ring
  rw [key]
  have hn : ∀ n : ℤ, ((n : ℂ)) ∈ K := fun n => by simpa using K.intCast_mem n
  exact K.div_mem (K.sub_mem (K.div_mem (K.sub_mem h3 h1) (K.sub_mem (hn n₃) (hn n₁)))
    (K.div_mem (K.sub_mem h2 h1) (K.sub_mem (hn n₂) (hn n₁)))) (K.sub_mem (hn n₃) (hn n₂))
