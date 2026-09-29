-- Prove2me | solution 1 for BookProof.QgHermiteCore.ExpBounded.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:06:48.904706+00:00
-- url     : https://prove2.me/submissions/11fcb9c3-8f7a-42e0-82a8-e040f802ef3d

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Basic
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E]

theorem solution {f : E → ℝ}
    (hf : ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |f x| ≤ C * Real.exp (c * ‖x‖)) (a : ℝ) :
    ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |a * f x| ≤ C * Real.exp (c * ‖x‖) := by
  rcases hf with ⟨C, c, hc, hf⟩
  refine ⟨|a| * C, c, hc, ?_⟩
  intro x
  simpa only [abs_mul, mul_assoc] using mul_le_mul_of_nonneg_left (hf x) (abs_nonneg a)
#print axioms solution
