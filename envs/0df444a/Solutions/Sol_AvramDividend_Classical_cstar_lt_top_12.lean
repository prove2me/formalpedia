-- Prove2me | solution 12 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:18:34.182981+00:00
-- url     : https://prove2.me/submissions/ea210c5c-f01e-4dde-a9c6-55db6ae739a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_deriv_continuous_positive_axis_growth

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Barrier finiteness reduced exactly to positive-axis derivative continuity
and derivative coercivity. The excursion representation sits below those two
inputs, so no tilted-normalisation or broad C1 theorem is needed here. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  have hcont : ContinuousOn (deriv W) (Ioi 0) :=
    scaleDeriv_continuous X hX q hq W hW
  have htop : Tendsto (deriv W) atTop atTop :=
    scaleDeriv_tendsto_atTop X hX q hq W hW
  exact cstar_finite_of_deriv_continuous_positive_axis_growth
    W hcont htop
