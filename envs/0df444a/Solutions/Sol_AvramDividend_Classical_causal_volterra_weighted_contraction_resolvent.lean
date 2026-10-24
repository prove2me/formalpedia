-- Prove2me | solution 1 for AvramDividend.Classical.causal_volterra_weighted_contraction_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:25:54.736749+00:00
-- url     : https://prove2.me/submissions/e1789b54-7a35-4ca9-92cb-6fa942077b36

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_affine_fixed_point_exists
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Undoing the weighted fixed point gives the continuous Volterra resolvent. -/
theorem solution
    (K : ℝ → ℝ) (a β weight : ℝ)
    (ha : 0 < a) (hweight : 0 < weight)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / weight +
      (∫ t in Ioi (0 : ℝ),
        |K t| * Real.exp (-weight * t) ∂volume) < a) :
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by
  obtain ⟨f, hf⟩ :=
    causal_weighted_BCF_affine_fixed_point_exists
      K a β weight ha hweight hK hsmall
  refine ⟨(fun x : ℝ => Real.exp (weight * x) *
    f ⟨max x 0, le_max_right x 0⟩), ?_, ?_⟩
  · exact (causal_weighted_BCF_extension_continuous f weight).continuousOn
  · intro x hx
    exact hf x hx
