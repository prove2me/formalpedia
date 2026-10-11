-- Prove2me | solution 1 for BookProof.WeakSecondDeriv.integral_eq_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:20:59.270521+00:00
-- url     : https://prove2.me/submissions/72fb7d22-0751-4567-a07f-6249ffeda663

-- Generated from ChapterWeakSecondDerivative.lean — solution of BookProof.WeakSecondDeriv.integral_eq_intervalIntegral
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv




open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {R a b : ℝ} (hR : 0 ≤ R)
    (hf : ∀ x, x ∉ Icc (-R) R → f x = 0) (ha : a < -R) (hb : R < b) :
    ∫ x, f x = ∫ x in a..b, f x := by

  have hab : a ≤ b := by linarith
  rw [intervalIntegral.integral_of_le hab, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
  refine hf x ?_
  simp only [mem_Icc, not_and_or, not_le]
  rcases hx with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)
