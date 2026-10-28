-- Prove2me | solution 1 for AvramDividend.Classical.restrictedPathLaw_scalar_lintegral_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:34:19.269523+00:00
-- url     : https://prove2.me/submissions/d505582c-541f-41ed-9d58-5920f1613a5a

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- A scaled restricted path law evaluates all measurable nonnegative stopped-history rewards. -/
theorem solution
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (Y : Ω → β) (hY : Measurable Y) (ν : Measure β)
    (hLaw : Measure.map Y (P.restrict A) = (P A) • ν)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, Set.indicator A (fun ω' => g (Y ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂ν) := by
  calc
    (∫⁻ ω, Set.indicator A (fun ω' => g (Y ω')) ω ∂P) =
        ∫⁻ ω, g (Y ω) ∂(P.restrict A) :=
      lintegral_indicator hA (fun ω => g (Y ω))
    _ = ∫⁻ y, g y ∂(Measure.map Y (P.restrict A)) :=
      (lintegral_map hg hY).symm
    _ = ∫⁻ y, g y ∂((P A) • ν) := by rw [hLaw]
    _ = P A * (∫⁻ y, g y ∂ν) := by
      rw [lintegral_smul_measure]
      exact smul_eq_mul _ _
