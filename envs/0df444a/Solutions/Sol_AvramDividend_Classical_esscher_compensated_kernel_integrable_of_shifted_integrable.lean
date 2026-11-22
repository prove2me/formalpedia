-- Prove2me | solution 1 for AvramDividend.Classical.esscher_compensated_kernel_integrable_of_shifted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:11:42.716816+00:00
-- url     : https://prove2.me/submissions/553abb1f-6d72-4ad8-b6d4-f9396a6eeb8d

import Mathlib
open MeasureTheory Set
theorem solution (κ : ℝ → ℝ) (φ s : ℝ)
    (hNext : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-((φ + s) * t))) * κ t) (Ioi 0))
    (hBase : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-(φ * t))) * κ t) (Ioi 0)) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(φ * t)) *
        (1 - Real.exp (-(s * t))) * κ t) (Ioi 0) := by
  have h := hNext.sub hBase
  convert h using 1
  funext t
  have he : Real.exp (-((φ+s)*t)) = Real.exp (-(φ*t)) * Real.exp (-(s*t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Pi.sub_apply] 
  rw [he]
  ring
#print axioms solution
