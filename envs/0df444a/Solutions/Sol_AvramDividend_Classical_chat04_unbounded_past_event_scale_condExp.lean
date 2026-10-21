-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_past_event_scale_condExp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T04:25:03.707928+00:00
-- url     : https://prove2.me/submissions/19764825-d141-4829-83b3-a315f19a7038

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_scale_past_event_condExp
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    P[A.indicator (fun ω => W (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      A.indicator (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P) := by
  -- The q-scale semigroup harmonicity, with the fixed-time integrability
  -- supplied by the unbounded-variation integrability theorem.
  have hInt : Integrable (fun ω => W (x + X.X (t - s) ω)) P :=
    AvramDividend.Classical.chat04_unbounded_scale_fixed_time_integrable
      X q hq W hW hnbv x (t - s)
  exact AvramDividend.Classical.chat04_shifted_scale_past_event_condExp
    X q W hW s t hst x A hA hInt
