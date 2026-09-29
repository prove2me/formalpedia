-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockManyMode.modeShift_shift_ne
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:42:00.509339+00:00
-- url     : https://prove2.me/submissions/738846fe-663b-48ee-893f-f4e6e1afaa26

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
set_option autoImplicit false

theorem solution {d : ℕ} (i i₀ : Fin d) :
    Function.update (Function.update (0 : Fin d → ℕ) i₀ 2) i
      ((Function.update (0 : Fin d → ℕ) i₀ 2) i + 2) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp only [Function.update_self, Pi.zero_apply] at hi
  omega
#print axioms solution
