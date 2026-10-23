-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_of_signed_laplace_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:07:36.489968+00:00
-- url     : https://prove2.me/submissions/0c995a9e-30b1-480e-9364-f8131bcb70d8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Identifying the Laplace transform with a C1 function transfers C1 regularity. -/
theorem solution
    (V G : ℝ → ℝ) (b : ℝ)
    (hVcont : ContinuousOn V (Ioi (0 : ℝ)))
    (hG : ContDiffOn ℝ 1 G (Ioi (0 : ℝ)))
    (hLap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * V x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * G x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * V x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * G x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  have hGcont : ContinuousOn G (Ioi (0 : ℝ)) := hG.continuousOn
  have hEq := continuousOn_Ioi_eq_of_laplace_eq_signed
    V G b hVcont hGcont hLap
  apply hG.congr
  intro x hx
  exact hEq x hx
