-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:02:26.18117+00:00
-- url     : https://prove2.me/submissions/bbcc1464-002c-4091-815a-f723b2100de2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn

open AvramDividend.Classical MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Locally bounded Neumann corrections preserve integrability of the reflected kernel. -/
theorem solution
    (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hB : ∀ x : ℝ, IntegrableOn
      (fun s : ℝ => B (x - s)) (Ioc (0 : ℝ) x) volume)
    (hMeas : ∀ x : ℝ, ∀ i : ℕ, AEStronglyMeasurable
      (Q i) (volume.restrict (Ioc (0 : ℝ) x)))
    (hBound : ∀ x : ℝ, ∀ i : ℕ, ∃ C : ℝ,
      ∀ s ∈ Ioc (0 : ℝ) x, ‖Q i s‖ ≤ C) :
    ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume := by
  intro m x i hi
  obtain ⟨C, hC⟩ := hBound x i
  apply (hB x).mul_bdd (hMeas x i)
  exact (ae_restrict_mem measurableSet_Ioc).mono (fun s hs => hC s hs)
