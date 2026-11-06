-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f5_zero_nu_same_space_levy_ito_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:53:20.68623+00:00
-- url     : https://prove2.me/submissions/cc2e3976-9a51-4e80-bca4-d15d04740a27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- In the zero-jump branch the same original X is its own Gaussian
component and both original jump fields vanish identically. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) :
    ∃ (Y : SpectrallyNegativeLevy P 𝓕)
      (Jsmall Jlarge : ℝ≥0 → Ω → ℝ),
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ (t : ℝ≥0) (ω : Ω),
        X.X t ω = (t : ℝ) * X.c +
          (Y.X t ω - (t : ℝ) * Y.c) +
          Jsmall t ω + Jlarge t ω) := by
  refine ⟨X, (fun _ _ => 0), (fun _ _ => 0), hν, rfl, ?_⟩
  intro t ω
  ring
