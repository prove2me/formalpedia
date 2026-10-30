-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_unbounded_deterministic_killed_qscale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:51:12.435151+00:00
-- url     : https://prove2.me/submissions/00b4678a-b823-4b8a-bb6d-2e461d9e3c1b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_deterministic_killed_qscale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- Genuine original-P deterministic killed q-scale harmonicity with the
exact unbounded-variation hypotheses of the canonical be9 stopped target. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω ∂P) =
      W x := by
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  exact avram_root29_01_deterministic_killed_qscale
    X q φ hq hφ hroot W hW x t
