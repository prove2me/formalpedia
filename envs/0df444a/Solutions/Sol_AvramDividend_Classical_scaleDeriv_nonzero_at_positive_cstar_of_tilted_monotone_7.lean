-- Prove2me | solution 7 for AvramDividend.Classical.scaleDeriv_nonzero_at_positive_cstar_of_tilted_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:12:34.853528+00:00
-- url     : https://prove2.me/submissions/14512011-36f4-464b-9ae2-54e051940548
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The normaliser at a positive optimal barrier is nonzero once the
    canonical barrier has been shown finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by
  have hfinite : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hpositive : 0 < (cstar W).toReal :=
    (ENNReal.toReal_pos_iff).mpr ⟨hc, hfinite⟩
  exact scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
    X hX q hq W hW hpositive hpos hdiff htilt
