-- Prove2me | solution 1 for AvramDividend.Classical.chat04_standing_past_event_scale_condExp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:44:56.231039+00:00
-- url     : https://prove2.me/submissions/7b11ce30-cace-4308-999a-bfa13090a6ba

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_scale_past_event_condExp
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Conditional q-scale Markov expectation after any historical survival event,
under the exact Standing and positive discount assumptions. Both the
integrability theorem and past-event conditional law are already Proved.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    P[A.indicator (fun ω => W (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      A.indicator (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P) := by
  have hInt :
      Integrable (fun ω => W (x + X.X (t - s) ω)) P :=
    AvramDividend.Classical.chat04_standing_scale_fixed_time_integrable
      X hX q hq W hW x (t - s)
  exact AvramDividend.Classical.chat04_shifted_scale_past_event_condExp
    X q W hW s t hst x A hA hInt
