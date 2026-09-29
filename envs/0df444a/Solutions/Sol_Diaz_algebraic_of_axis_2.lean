-- Prove2me | solution 2 for Diaz.algebraic_of_axis
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:21:01.205603+00:00
-- url     : https://prove2.me/submissions/2010c236-e67a-449c-bfce-7844453746e4

/-
`Diaz.algebraic_of_axis` through `Diaz.normal_form`: the first clause of that
node is `‖u‖ algebraic ↔ u ū algebraic`, and on either axis `u² = ±(u ū)`, so
`u²` and hence `u` is algebraic.  The degenerate case `u = 0` is immediate and
is the one place `normal_form`'s hypothesis `u ≠ 0` has to be split off.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_normal_form

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {u : ℂ} (hax : conj u = u ∨ conj u = -u)
    (h : IsAlgebraic ℚ ‖u‖) : IsAlgebraic ℚ u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · exact isAlgebraic_zero
  have hmod : IsAlgebraic ℚ (u * conj u) := (Diaz.normal_form hu0).1.mp h
  have h2 : IsAlgebraic ℚ (u ^ 2) := by
    rcases hax with hx | hx
    · have e : u ^ 2 = u * conj u := by rw [hx]; ring
      rw [e]; exact hmod
    · have e : u ^ 2 = -(u * conj u) := by rw [hx]; ring
      rw [e]; exact hmod.neg
  exact h2.of_pow two_pos
