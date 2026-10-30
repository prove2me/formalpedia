-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_killed_discounted_scale_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:10:52.82552+00:00
-- url     : https://prove2.me/submissions/4dcd0f9e-fb36-4067-8577-0728c12566cb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_martingale_from_source

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The canonical unbounded-variation killed martingale follows directly
from the independently accepted source-faithful all-reserve theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) :
    Martingale
      (fun t ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω)
      𝓕 P := by
  exact avram_root29_01_unbounded_killed_martingale_from_source
    X hnbv q hq W hW x
