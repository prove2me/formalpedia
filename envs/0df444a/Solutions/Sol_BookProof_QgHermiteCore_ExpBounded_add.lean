-- Prove2me | solution 1 for BookProof.QgHermiteCore.ExpBounded.add
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:40:04.85792+00:00
-- url     : https://prove2.me/submissions/359e8d02-24de-4c31-be63-9bfc3865d309

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Basic

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E]

theorem solution {f g : E → ℝ}
    (hf : ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |f x| ≤ C * Real.exp (c * ‖x‖))
    (hg : ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |g x| ≤ C * Real.exp (c * ‖x‖)) :
    ∃ C c : ℝ, 0 ≤ c ∧ ∀ x, |f x + g x| ≤ C * Real.exp (c * ‖x‖) := by
  rcases hf with ⟨C, c, hc, hf⟩
  rcases hg with ⟨D, d, hd, hg⟩
  have hC : 0 ≤ C := by simpa using le_trans (abs_nonneg _) (hf 0)
  have hD : 0 ≤ D := by simpa using le_trans (abs_nonneg _) (hg 0)
  refine ⟨C + D, c + d, add_nonneg hc hd, ?_⟩
  intro x
  have hec : Real.exp (c * ‖x‖) ≤ Real.exp ((c + d) * ‖x‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hd) (norm_nonneg x))
  have hed : Real.exp (d * ‖x‖) ≤ Real.exp ((c + d) * ‖x‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hc) (norm_nonneg x))
  calc
    |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ C * Real.exp ((c + d) * ‖x‖) + D * Real.exp ((c + d) * ‖x‖) :=
      add_le_add ((hf x).trans (mul_le_mul_of_nonneg_left hec hC))
        ((hg x).trans (mul_le_mul_of_nonneg_left hed hD))
    _ = (C + D) * Real.exp ((c + d) * ‖x‖) := (add_mul _ _ _).symm

#print axioms solution
