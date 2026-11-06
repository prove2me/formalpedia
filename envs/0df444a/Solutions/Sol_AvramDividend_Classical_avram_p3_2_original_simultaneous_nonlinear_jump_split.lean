-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_simultaneous_nonlinear_jump_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:45:48.6572+00:00
-- url     : https://prove2.me/submissions/448972b5-3d37-42f5-8d5d-ff5ddfbe73b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Literal original X/D nonlinear reserve jump splits at the pre-rightpayment
reserve. The source jump and dividend atom can occur simultaneously. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (ω : Ω) (t : ℝ≥0) (lX : ℝ) :
    w (x + X.X t ω - rightLimit D t ω) -
      w (x + lX - D t ω) =
      (w (x + X.X t ω - D t ω) -
        w (x + lX - D t ω)) +
      (w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X t ω - D t ω)) := by
  ring
