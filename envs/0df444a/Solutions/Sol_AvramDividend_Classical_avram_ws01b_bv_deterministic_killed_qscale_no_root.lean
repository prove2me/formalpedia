-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_deterministic_killed_qscale_no_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:55:19.836532+00:00
-- url     : https://prove2.me/submissions/c4dc3984-0b2b-40d2-81ba-29c78ad919f4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_deterministic_killed_qscale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A standing BV original Lévy process has its genuine all-reserve
closed-history killed q-scale fixed point at every deterministic time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation) (x : ℝ) (t : ℝ≥0) :
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω ∂P) =
      W x := by
  obtain ⟨φ, hφ, hroot⟩ := bv_positive_esscher_root X hX q hq hBV
  exact avram_root29_01_deterministic_killed_qscale
    X q φ hq hφ hroot W hW x t
