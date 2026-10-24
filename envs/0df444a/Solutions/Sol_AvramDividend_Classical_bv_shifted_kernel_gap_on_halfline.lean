-- Prove2me | solution 1 for AvramDividend.Classical.bv_shifted_kernel_gap_on_halfline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:50:12.281662+00:00
-- url     : https://prove2.me/submissions/121e5378-4776-40f9-af73-47a3fd2f0fca

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_shifted_kernel_gap_on_halfline_canonical
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
The canonical Esscher shift q / drift is a positive witness for the
general existential BV shifted-kernel gap.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (φ b : ℝ), 0 < φ ∧ 0 < b ∧
      ∀ s : ℝ, b ≤ s →
        (∫⁻ z : ℝ≥0, ENNReal.ofReal
          ((1 - Real.exp (-(s + φ) * (z : ℝ))) / s)
          ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) <
          ENNReal.ofReal X.drift := by
  obtain ⟨b, hb, hgap⟩ :=
    bv_shifted_kernel_gap_on_halfline_canonical X hX q hq hbv
  refine ⟨q / X.drift, b, div_pos hq
    (bv_standing_drift_pos X hX hbv).1, hb, ?_⟩
  intro s hs
  exact hgap s hs
