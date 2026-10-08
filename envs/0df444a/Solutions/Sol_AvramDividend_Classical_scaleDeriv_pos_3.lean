-- Prove2me | solution 3 for AvramDividend.Classical.scaleDeriv_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T18:05:34.272773+00:00
-- url     : https://prove2.me/submissions/20323408-3781-4795-8273-154d4bb024bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strict positivity of W' reduced directly to strict scale-function
positivity and the Esscher excursion-tail derivative identity. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  obtain ⟨φ, μ, hφ, hnull, hfin, hdiff, hrepr⟩ :=
    scaleFunction_excursion_tail_derivative_representation
      X hX q hq W hW
  intro x hx
  rw [hrepr x hx]
  have hWpos : 0 < W x :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW x hx
  have htail : 0 ≤ μ.real (Ici x) := measureReal_nonneg
  exact mul_pos hWpos (by linarith)
