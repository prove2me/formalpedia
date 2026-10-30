-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:54:08.017086+00:00
-- url     : https://prove2.me/submissions/615ca0df-ad7c-4748-aa15-4228f9904018

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_hasDerivAt_of_deriv_ne_zero
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_lower_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_bound
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine reflected-barrier ratio needs only a nonzero local derivative. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hNe : deriv W a ≠ 0) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by
  have hD : HasDerivAt W (deriv W a) a :=
    hasDerivAt_of_deriv_ne_zero hNe
  have hLo :=
    barrierSupValue_stopped_renewal_lower_bound
      X hX q hq W hW a ha hD hNe
  have hHi :=
    barrierSupValue_stopped_renewal_upper_bound
      X hX q hq W hW a ha hD hNe
  exact barrierSupValue_of_stopped_renewal_bounds
    X hX q hq W hW a ha hD hNe hLo hHi
