-- Prove2me | solution 1 for AvramDividend.Classical.sigmaFinite_absolutelyContinuous_has_real_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:52:19.496992+00:00
-- url     : https://prove2.me/submissions/38a224b2-a311-4ce1-9866-7eb1248dcf03

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- A sigma-finite absolutely continuous kernel admits a measurable nonnegative real density. -/
theorem solution (μ : Measure ℝ) [SigmaFinite μ]
    (hμac : μ ≪ (volume : Measure ℝ)) :
    ∃ K : ℝ → ℝ, Measurable K ∧
      (∀ x : ℝ, 0 ≤ K x) ∧
      μ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x)) := by
  let K : ℝ → ℝ := fun x => (μ.rnDeriv volume x).toReal
  have hKmeas : Measurable K :=
    ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv μ volume)
  have hKpos : ∀ x : ℝ, 0 ≤ K x := by
    intro x
    exact ENNReal.toReal_nonneg
  have hKae : (fun x : ℝ => ENNReal.ofReal (K x)) =ᵐ[volume]
      (fun x : ℝ => μ.rnDeriv volume x) := by
    filter_upwards [Measure.rnDeriv_lt_top μ volume] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  have hKmeasure :
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x)) = μ :=
    (withDensity_congr_ae hKae).trans
      (Measure.withDensity_rnDeriv_eq μ volume hμac)
  exact ⟨K, hKmeas, hKpos, hKmeasure.symm⟩
