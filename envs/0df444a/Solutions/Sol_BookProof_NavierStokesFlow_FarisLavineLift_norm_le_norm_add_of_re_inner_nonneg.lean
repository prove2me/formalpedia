-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.norm_le_norm_add_of_re_inner_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:35:45.574243+00:00
-- url     : https://prove2.me/submissions/2c21d7e0-77fe-4c2b-9e01-2e20f7c02b1d

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem solution {x y : F} (h : 0 ≤ (inner ℂ x y : ℂ).re) :
    ‖x‖ ≤ ‖x + y‖ := by
  have hsq := norm_add_sq (𝕜 := ℂ) x y
  change ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * (inner ℂ x y).re + ‖y‖ ^ 2 at hsq
  nlinarith [norm_nonneg x, norm_nonneg (x + y), sq_nonneg ‖y‖]

#print axioms solution
