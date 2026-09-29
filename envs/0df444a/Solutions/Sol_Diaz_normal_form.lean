-- Prove2me | solution 1 for Diaz.normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:02:19.445104+00:00
-- url     : https://prove2.me/submissions/0faa3a3f-f520-4b3f-b5fc-bb69a1830e7a

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

private theorem p21_alg_ofReal_iff {x : ℝ} : IsAlgebraic ℚ ((x : ℂ)) ↔ IsAlgebraic ℚ x :=
  isAlgebraic_algebraMap_iff (A := ℂ) (S := ℝ) (R := ℚ) Complex.ofReal_injective

private theorem p21_mul_conj_eq (u : ℂ) : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.mul_conj]; norm_cast; rw [Complex.normSq_eq_norm_sq]

open Diaz in
theorem solution {u : ℂ} (hu : u ≠ 0) :
    (IsAlgebraic ℚ ‖u‖ ↔ IsAlgebraic ℚ (u * conj u)) ∧
      (IsAlgebraic ℚ (u * conj u) ↔
        ∃ ρ : ℝ, 0 < ρ ∧ IsAlgebraic ℚ ρ ∧ u * conj u = (ρ : ℂ)) := by
  have key : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := p21_mul_conj_eq u
  have hpos : (0 : ℝ) < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu) 2
  constructor
  · rw [key]
    exact ⟨fun h => (p21_alg_ofReal_iff.mpr h).pow 2,
      fun h => p21_alg_ofReal_iff.mp (h.of_pow two_pos)⟩
  · constructor
    · intro h
      refine ⟨‖u‖ ^ 2, hpos, ?_, ?_⟩
      · refine p21_alg_ofReal_iff.mp ?_
        push_cast
        rw [← key]; exact h
      · rw [key]; push_cast; ring
    · rintro ⟨ρ, -, hρ, heq⟩
      rw [heq]; exact p21_alg_ofReal_iff.mpr hρ
