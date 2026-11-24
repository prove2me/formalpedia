-- Prove2me | solution 1 for Formalism.QuantumDeterminants.tsupport_star_fun
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T10:37:13.714188+00:00
-- url     : https://prove2.me/submissions/44b4f836-6906-40a2-b313-70897632238a

import Mathlib

theorem solution {m : ℕ} (g : (Fin m → ℂ) → ℂ) :
    tsupport (fun y => star (g y)) = tsupport g := by
  simp [tsupport, Function.support, star_ne_zero]
