-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_semigroup_constant_of_laplace_and_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:20:16.253376+00:00
-- url     : https://prove2.me/submissions/a7c95848-5ed8-4036-9735-ef2773c962aa

import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

/-- Equal Laplace transforms and right continuity force a killed-semigroup reward
    to equal its initial constant at every nonnegative time. -/
theorem solution
    (g : ℝ → ℝ) (c b : ℝ) (hc : 0 ≤ c)
    (hgzero : g 0 = c)
    (hgright : ∀ x : ℝ, 0 < x → ContinuousWithinAt g (Ici x) x)
    (hgmeas : AEMeasurable g (volume.restrict (Ioi 0)))
    (hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * c) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * g x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * c) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * g x) :
    ∀ t : ℝ, 0 ≤ t → g t = c := by
  have hconst : ContinuousOn (fun _ : ℝ => c) (Ioi 0) :=
    continuousOn_const
  have hpositive : ∀ u : ℝ, 0 < u → c = g u :=
    continuous_rightContinuous_Ioi_eq_of_laplace_eq
      (fun _ : ℝ => c) g b hconst hgright hgmeas
      (by intro u hu; exact hc) hgnonneg hlap
  intro t ht
  rcases lt_or_eq_of_le ht with hpos | hzero
  · exact (hpositive t hpos).symm
  · subst t
    exact hgzero
