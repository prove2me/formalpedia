-- Prove2me | solution 11 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:25:13.672011+00:00
-- url     : https://prove2.me/submissions/117494ef-a0e1-47b1-9f2b-499f9f636178
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_normalized_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Direct cstar finiteness reduction that no longer depends on the broad
C1 scale-function theorem. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  obtain ⟨hpos, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hW1 : 0 < W 1 := hpos 1 (by norm_num)
  obtain ⟨φe, μ, hφe, hnull, hfin, hdiff, hrepr⟩ :=
    scaleFunction_excursion_tail_derivative_representation
      X hX q hq W hW
  have hcont : ContinuousOn (deriv W) (Ioi 0) :=
    scaleDeriv_continuous X hX q hq W hW
  exact cstar_finite_of_normalized_monotone
    W φ hφ hW1 htilt hdiff hcont
