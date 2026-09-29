-- Prove2me | solution 1 for Diaz.elliptic_axis_alignment
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:12:01.998031+00:00
-- url     : https://prove2.me/submissions/4bef96a1-bdd3-4a44-9222-3f08b3cc9b6a

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {u : ℂ} (hu : ¬ IsAlgebraic ℚ u)
    (hn : IsAlgebraic ℚ (u * conj u)) :
    (conj u ≠ u ∧ conj u ≠ -u) ∧ ∀ γ : ℂ, IsAlgebraic ℚ γ → conj u ≠ γ * u := by
  have key : ∀ γ : ℂ, IsAlgebraic ℚ γ → conj u ≠ γ * u := by
    intro γ hγ hcon
    have hu0 : u ≠ 0 := by rintro rfl; exact hu (isAlgebraic_zero)
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      apply hu0
      have h0 : conj u = 0 := by rw [hcon]; ring
      have := congrArg (starRingEnd ℂ) h0
      simpa using this
    have h1 : u * conj u = γ * u ^ 2 := by rw [hcon]; ring
    have h2 : (u : ℂ) ^ 2 = (u * conj u) / γ := by rw [h1]; field_simp
    have h3 : IsAlgebraic ℚ ((u : ℂ) ^ 2) := by
      rw [h2]
      exact mem_algebraicClosure_iff.mp
        (div_mem (mem_algebraicClosure_iff.mpr hn) (mem_algebraicClosure_iff.mpr hγ))
    exact hu (h3.of_pow (by norm_num))
  refine ⟨⟨?_, ?_⟩, key⟩
  · intro h; exact key 1 isAlgebraic_one (by simpa using h)
  · intro h; exact key (-1) (isAlgebraic_one.neg) (by simpa using h)
