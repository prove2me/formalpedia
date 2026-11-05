-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:43:55.314422+00:00
-- url     : https://prove2.me/submissions/ecfcba44-360a-4cbc-b758-723367b937bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite original-clock sampled stopping index evaluates the unchanged source process at its grid time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ≥0 → Ω → ℝ) (e : ℕ → ℝ≥0)
    (K : Ω → ℕ) :
    ∀ ω, stoppedValue (fun i : ℕ => f (e i))
      (fun ω => (K ω : WithTop ℕ)) ω = f (e (K ω)) ω := by
  intro ω
  rfl
