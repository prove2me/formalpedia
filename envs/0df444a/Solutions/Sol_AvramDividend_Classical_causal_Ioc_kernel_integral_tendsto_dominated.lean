-- Prove2me | solution 1 for AvramDividend.Classical.causal_Ioc_kernel_integral_tendsto_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:26:41.074734+00:00
-- url     : https://prove2.me/submissions/4756ccbc-a7f4-475b-b62c-2c77745e4649

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Dominated convergence through a finite-horizon causal kernel integral. -/
theorem solution
    (B : ℝ → ℝ) (f : ℕ → ℝ → ℝ) (g D : ℝ → ℝ) (x : ℝ)
    (hMeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun s : ℝ => B (x - s) * f n s)
      (volume.restrict (Ioc (0 : ℝ) x)))
    (hD : IntegrableOn D (Ioc (0 : ℝ) x) volume)
    (hbound : ∀ n : ℕ,
      ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
        ‖B (x - s) * f n s‖ ≤ D s)
    (hpoint : ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
      Tendsto (fun n : ℕ => f n s) atTop (nhds (g s))) :
    Tendsto (fun n : ℕ =>
      ∫ s in Ioc (0 : ℝ) x, B (x - s) * f n s ∂volume)
      atTop (nhds
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume)) := by
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    D hMeas hD hbound
    (hpoint.mono (fun s hs => hs.const_mul (B (x - s))))
