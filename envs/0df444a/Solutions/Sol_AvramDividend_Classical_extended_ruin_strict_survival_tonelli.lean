-- Prove2me | solution 1 for AvramDividend.Classical.extended_ruin_strict_survival_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:58:02.130427+00:00
-- url     : https://prove2.me/submissions/1fb45035-dbf1-4b25-944d-569a344942d0

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ ω, ∫⁻ t in Ioi (0 : ℝ),
      (if ENNReal.ofReal t < τ ω then w t else 0) ∂volume ∂P) =
    (∫⁻ t in Ioi (0 : ℝ),
      P {ω : Ω | ENNReal.ofReal t < τ ω} * w t ∂volume) := by
  let A : Set (ℝ × Ω) :=
    {p | 0 < p.1 ∧ ENNReal.ofReal p.1 < τ p.2}
  let F : ℝ × Ω → ℝ≥0∞ :=
    A.indicator (fun p => w p.1)
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt
        (ENNReal.measurable_ofReal.comp measurable_fst)
        (hτ.comp measurable_snd))
  have hF : Measurable F :=
    (hw.comp measurable_fst).indicator hA
  have hinner (ω : Ω) :
      (∫⁻ t in Ioi (0 : ℝ),
        (if ENNReal.ofReal t < τ ω then w t else 0) ∂volume) =
      (∫⁻ t, F (t, ω) ∂volume) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht : 0 < t
    · simp [F, A, Set.indicator_apply, ht]
    · simp [F, A, Set.indicator_apply, ht]
  have hprob (t : ℝ) :
      (∫⁻ ω, F (t, ω) ∂P) =
      (Ioi (0 : ℝ)).indicator
        (fun x => P {ω : Ω | ENNReal.ofReal x < τ ω} * w x) t := by
    by_cases ht : 0 < t
    · have heq : (fun ω => F (t, ω)) =
          {ω : Ω | ENNReal.ofReal t < τ ω}.indicator
            (fun _ => w t) := by
        funext ω
        simp [F, A, Set.indicator_apply, ht]
      rw [heq, lintegral_indicator_const
        (measurableSet_lt measurable_const hτ)]
      simp [Set.indicator_apply, ht, mul_comm]
    · have heq : (fun ω => F (t, ω)) = fun _ => 0 := by
        funext ω
        simp [F, A, Set.indicator_apply, ht]
      rw [heq]
      simp [Set.indicator_apply, ht]
  calc
    (∫⁻ ω, ∫⁻ t in Ioi (0 : ℝ),
      (if ENNReal.ofReal t < τ ω then w t else 0) ∂volume ∂P) =
        (∫⁻ ω, ∫⁻ t, F (t, ω) ∂volume ∂P) := by
          apply lintegral_congr
          intro ω
          exact hinner ω
    _ = (∫⁻ t, ∫⁻ ω, F (t, ω) ∂P ∂volume) := by
      exact (lintegral_lintegral_swap (μ := volume) (ν := P)
        (f := fun (t : ℝ) (ω : Ω) => F (t, ω)) hF.aemeasurable).symm
    _ = (∫⁻ t, (Ioi (0 : ℝ)).indicator
          (fun t => P {ω : Ω | ENNReal.ofReal t < τ ω} * w t) t ∂volume) := by
          apply lintegral_congr
          intro t
          exact hprob t
    _ = (∫⁻ t in Ioi (0 : ℝ),
      P {ω : Ω | ENNReal.ofReal t < τ ω} * w t ∂volume) :=
        lintegral_indicator measurableSet_Ioi _
