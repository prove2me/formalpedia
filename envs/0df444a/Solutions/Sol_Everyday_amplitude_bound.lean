-- Prove2me | solution 1 for Everyday.amplitude_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:23:18.380083+00:00
-- url     : https://prove2.me/submissions/c5272b1c-6d56-4dbb-a678-ddaf62df8b91

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open Everyday
/-- Quantum mechanics: the path integral is a coherent sum. On a finite
configuration space, the amplitude W = ∑_c exp(i S c) has modulus at
most the number of configurations — a finite sum of unit phases. Each
summand is a phase; the bound is the triangle inequality. -/


theorem solution (C : Type) [Fintype C] (S : C → ℝ) :
    ‖amplitude S‖ ≤ (Fintype.card C : ℝ) := by
  unfold amplitude
  calc _ ≤ ∑ c, ‖Complex.exp (Complex.I * (S c : ℂ))‖ := norm_sum_le _ _
    _ = ∑ c : C, (1:ℝ) := by
        congr 1; ext c; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
    _ = _ := by simp


