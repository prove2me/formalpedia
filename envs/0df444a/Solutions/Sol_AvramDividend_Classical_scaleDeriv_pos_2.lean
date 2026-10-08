-- Prove2me | solution 2 for AvramDividend.Classical.scaleDeriv_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:00:37.924855+00:00
-- url     : https://prove2.me/submissions/9084c181-3e54-4740-aa78-06b768a79a27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strict derivative positivity using differentiability from the excursion
representation, rather than the broader C1 regularity theorem. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  obtain ⟨φe, μ, hφe, hnull, hfin, hdiff, hrepr⟩ :=
    scaleFunction_excursion_tail_derivative_representation
      X hX q hq W hW
  obtain ⟨hpos, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  exact scaleDeriv_pos_of_tilted_positive_monotone
    X hX q hq W hW hpos hdiff ⟨φ, hφ, hmono⟩
