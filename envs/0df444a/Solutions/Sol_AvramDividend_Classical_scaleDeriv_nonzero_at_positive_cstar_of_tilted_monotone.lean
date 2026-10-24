-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_nonzero_at_positive_cstar_of_tilted_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:56:54.979258+00:00
-- url     : https://prove2.me/submissions/b6dc08eb-d35d-41d8-8239-9ebbb34574f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finiteness converts positivity of the extended barrier into
strict positivity of its real value, permitting the proved normaliser lemma. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by
  have hfinite : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hcReal : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos (ne_of_gt hc) (ne_of_lt hfinite)
  exact scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
    X hX q hq W hW hcReal hpos hdiff htilt
