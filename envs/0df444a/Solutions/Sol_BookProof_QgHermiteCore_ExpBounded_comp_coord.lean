-- Prove2me | solution 1 for BookProof.QgHermiteCore.ExpBounded.comp_coord
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:11:42.332767+00:00
-- url     : https://prove2.me/submissions/0d4858e2-52b7-4d35-8889-e169ab1a0937

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false

theorem solution {d : ℕ} {f : ℝ → ℝ}
    (hf : ∃ C c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, |f x| ≤ C * Real.exp (c * ‖x‖)) (i : Fin d) :
    ∃ C c : ℝ, 0 ≤ c ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      |f (x i)| ≤ C * Real.exp (c * ‖x‖) := by
  rcases hf with ⟨C, c, hc, hf⟩
  have hC : 0 ≤ C := by simpa using (abs_nonneg (f 0)).trans (hf 0)
  refine ⟨C, c, hc, ?_⟩
  intro x
  exact (hf (x i)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i) hc)) hC)
#print axioms solution
