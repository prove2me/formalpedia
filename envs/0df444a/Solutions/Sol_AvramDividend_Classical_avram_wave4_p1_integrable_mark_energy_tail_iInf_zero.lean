-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:42:29.887142+00:00
-- url     : https://prove2.me/submissions/e4503fe8-504b-41f7-a400-e0a8a7d82666

import Mathlib
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Integrable mark-energy tails vanish under a decreasing measurable
exhaustion towards the empty set, even for infinite-activity intensity. -/
theorem solution
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (f : E → ℝ≥0∞) (hf : Measurable f)
    (hfFinite : (∫⁻ z, f z ∂ν) ≠ ∞)
    (D : ℕ → Set E) (hDm : ∀ n, MeasurableSet (D n))
    (hDanti : Antitone D) (hDempty : (⋂ n, D n) = ∅) :
    (⨅ n, ∫⁻ z in D n, f z ∂ν) = 0 := by
  classical
  let ρ : Measure E := ν.withDensity f
  have hRho (s : Set E) (hs : MeasurableSet s) :
      ρ s = ∫⁻ z in s, f z ∂ν := by
    simpa [ρ] using (withDensity_apply f hs)
  have hRhoFinite : ρ Set.univ ≠ ∞ := by
    rw [hRho Set.univ MeasurableSet.univ]
    simpa using hfFinite
  have hFirstFinite : ρ (D 0) ≠ ∞ :=
    ne_top_of_le_ne_top hRhoFinite
      (measure_mono (Set.subset_univ (D 0)))
  have hInterMeasure : ρ (⋂ n, D n) = ⨅ n, ρ (D n) :=
    hDanti.measure_iInter
      (fun n => (hDm n).nullMeasurableSet)
      ⟨0, hFirstFinite⟩
  calc
    (⨅ n, ∫⁻ z in D n, f z ∂ν) =
        ⨅ n, ρ (D n) := by
      apply iInf_congr
      intro n
      exact (hRho (D n) (hDm n)).symm
    _ = ρ (⋂ n, D n) := hInterMeasure.symm
    _ = 0 := by simp [hDempty]
