-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_family_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:23:09.818877+00:00
-- url     : https://prove2.me/submissions/d2756517-812c-467e-ac74-d178e4518fa7

import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_lipschitz_bound
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Scale functions depend continuously on their nonnegative discount parameter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      ContinuousOn (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by
  intro x hx
  let C : ℝ := ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s)
  have hlip : LipschitzOnWith C.toNNReal
      (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by
    apply LipschitzOnWith.of_dist_le'
    intro a ha b hb
    have h := unbounded_scale_discount_family_lipschitz_bound
      X hnbv Q hQ W hW x hx b hb a ha
    simpa only [Real.dist_eq, mul_comm] using h
  exact hlip.continuousOn
