-- Prove2me | solution 1 for Disjunctive.VPolyhedral.violating_vertex_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T00:08:16.054754+00:00
-- url     : https://prove2.me/submissions/9031ed20-8cf8-49a6-9f66-11c4c37b6ab1

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

set_option autoImplicit false

open Disjunctive.VPolyhedral in
theorem solution {n m : ℕ} {Q : Type*} {Rh : Q → ℕ}
    (Atil : Matrix (Fin m) (Fin n) ℝ) (btil : Fin m → ℝ) (Dh : ∀ h, Matrix (Fin (Rh h)) (Fin n) ℝ)
    (d0h : ∀ h, Fin (Rh h) → ℝ) (xF : Fin n → ℝ) (alpha : Fin n → ℝ) (beta : ℝ)
    (hxF_tight : dotProduct alpha xF = beta)
    (x : Fin n → ℝ) (hx_cone : (x - xF, (1 : ℝ)) ∈ DisjunctiveCone Atil btil Dh d0h xF) :
    dotProduct alpha x < beta ↔ dotProduct alpha (x - xF) < 0 := by
  rw [dotProduct_sub, hxF_tight]
  constructor <;> intro h <;> linarith

