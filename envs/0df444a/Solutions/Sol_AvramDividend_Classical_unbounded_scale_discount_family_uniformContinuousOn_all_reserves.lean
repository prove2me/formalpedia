-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_family_uniformContinuousOn_all_reserves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:53:48.847631+00:00
-- url     : https://prove2.me/submissions/0c8c049f-08be-44ed-981d-54e70e4319f0

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_lipschitz_bound
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The q-scale family is uniformly continuous in q at every real reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, UniformContinuousOn (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by
  intro x
  by_cases hx : 0 < x
  · let C : ℝ := ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s)
    have hlip : LipschitzOnWith C.toNNReal
        (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by
      apply LipschitzOnWith.of_dist_le'
      intro a ha b hb
      have h := unbounded_scale_discount_family_lipschitz_bound
        X hnbv Q hQ W hW x hx b hb a ha
      simpa only [Real.dist_eq, mul_comm] using h
    exact hlip.uniformContinuousOn
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hz : ∀ q ∈ Icc (0 : ℝ) Q, W q x = 0 := by
      intro q hq
      rcases lt_or_eq_of_le hxle with hneg | heq
      · exact (hW q hq).1 x hneg
      · subst x
        exact unbounded_scale_zero_origin_nonnegative_discount X hnbv q hq.1 (W q) (hW q hq)
    have hlip : LipschitzOnWith (Real.toNNReal (0 : ℝ))
        (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by
      apply LipschitzOnWith.of_dist_le'
      intro a ha b hb
      change dist (W a x) (W b x) ≤ (0 : ℝ) * dist a b
      simp [hz a ha, hz b hb]
    exact hlip.uniformContinuousOn
