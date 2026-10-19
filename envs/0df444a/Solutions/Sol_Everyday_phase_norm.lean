-- Prove2me | solution 1 for Everyday.phase_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:23:04.387425+00:00
-- url     : https://prove2.me/submissions/291e8387-ae7d-470d-973d-6f4ca84d4d16

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open Everyday
/-- Quantum mechanics: the exponential of i times a real number is a
phase — the amplitude exp(iS) contributed by a single configuration of
real action S has modulus exactly one. -/


theorem solution (s : ℝ) : ‖Complex.exp (Complex.I * (s : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I s


