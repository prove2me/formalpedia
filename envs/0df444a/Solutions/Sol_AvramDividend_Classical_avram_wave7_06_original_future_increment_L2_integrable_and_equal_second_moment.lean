-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_future_increment_L2_integrable_and_equal_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:41:22.872254+00:00
-- url     : https://prove2.me/submissions/b8d11917-18ce-46a2-be9e-26beaac46f99

import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source future-increment second moments transport under genuine L² integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (fun ω => (X.X t ω) ^ (2 : ℕ)) P) :
    Integrable
      (fun ω => (X.X (s + t) ω - X.X s ω) ^ (2 : ℕ)) P ∧
    (∫ ω, (X.X (s + t) ω - X.X s ω) ^ (2 : ℕ) ∂P) =
      ∫ ω, (X.X t ω) ^ (2 : ℕ) ∂P := by
  have hs : s ≤ s + t := by simp
  have hLaw :
      IdentDistrib
        (fun ω => X.X (s + t) ω - X.X s ω)
        (X.X t) P P := by
    simpa only [add_tsub_cancel_left] using
      (X.stationaryIncrements s (s + t) hs)
  have hSquare : Measurable (fun x : ℝ => x ^ (2 : ℕ)) := by
    fun_prop
  have hSquareLaw :
      IdentDistrib
        (fun ω => (X.X (s + t) ω - X.X s ω) ^ (2 : ℕ))
        (fun ω => (X.X t ω) ^ (2 : ℕ)) P P := by
    simpa only [Function.comp_def] using (hLaw.comp hSquare)
  exact ⟨hSquareLaw.integrable_iff.mpr hInt, hSquareLaw.integral_eq⟩
