-- Prove2me | solution 1 for AvramDividend.Classical.lower_survival_exponential_tail_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:50:39.739024+00:00
-- url     : https://prove2.me/submissions/722f607a-ffeb-4e03-83f7-2975ee6b2c2a

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set
theorem solution
    (m θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-θ * x)) (Ioi (max 0 (-m))) ∧
      (∫ x in Ioi (max 0 (-m)), Real.exp (-θ * x)) =
        Real.exp (-θ * max 0 (-m)) / θ := by 
  refine ⟨integrableOn_exp_mul_Ioi (by linarith) _, ?_⟩
  rw [integral_exp_mul_Ioi (by linarith)]
  field_simp
