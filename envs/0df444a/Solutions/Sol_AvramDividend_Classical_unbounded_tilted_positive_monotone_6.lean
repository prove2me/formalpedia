-- Prove2me | solution 6 for AvramDividend.Classical.unbounded_tilted_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:39:40.54863+00:00
-- url     : https://prove2.me/submissions/ce644124-1297-4ecd-a1ed-7d02b407c792

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The unbounded corrected exit identity supplies the remaining
probabilistic hypothesis for Esscher positivity and monotonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧
        MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  obtain ⟨hpos, φ, hφ, _hroot, hmono⟩ :=
    AvramDividend.Classical.unbounded_positive_tilt_of_corrected_exit
      X q hq W hW hnbv
      (fun a x ha hx0 hxa =>
        AvramDividend.Classical.unbounded_corrected_exit_scale_identity
          X q hq W hW hnbv a x ha hx0 hxa)
  refine ⟨hpos, φ, hφ, ?_⟩
  simpa only [neg_mul] using hmono
