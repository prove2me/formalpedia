-- Prove2me | solution 1 for BookProof.QgHermiteCore.ExpBounded.mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:40:03.962721+00:00
-- url     : https://prove2.me/submissions/c528b92d-12b2-43ea-8182-1ade81b9ba3c

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E]

theorem solution {f g : E → ℝ}
    (hf : ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |f x| ≤ C * Real.exp (c * ‖x‖))
    (hg : ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |g x| ≤ C * Real.exp (c * ‖x‖)) :
    ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |f x * g x| ≤ C * Real.exp (c * ‖x‖) := by
  rcases hf with ⟨C, c, hc, hf⟩
  rcases hg with ⟨D, d, hd, hg⟩
  refine ⟨C * D, c + d, add_nonneg hc hd, ?_⟩
  intro x
  rw [abs_mul]
  calc
    |f x| * |g x| ≤ (C * Real.exp (c * ‖x‖)) * (D * Real.exp (d * ‖x‖)) :=
      mul_le_mul (hf x) (hg x) (abs_nonneg _) (le_trans (abs_nonneg _) (hf x))
    _ = (C * D) * Real.exp ((c + d) * ‖x‖) := by
      rw [add_mul, Real.exp_add]
      ring

#print axioms solution
