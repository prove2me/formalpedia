-- Prove2me | solution 1 for AvramDividend.Classical.positive_psi_implies_upward_increment_positive_measure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:47:17.101992+00:00
-- url     : https://prove2.me/submissions/d59bb89a-9476-4f97-8c25-55715ac21dc1

import Theorems.Thm_AvramDividend_Classical_positive_psi_excludes_nonpositive_one_increment_ae
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 < X.ψ θ) :
    0 < P {ω : Ω | 0 < X.X 1 ω} := by
  rw [pos_iff_ne_zero]
  intro h0
  apply AvramDividend.Classical.positive_psi_excludes_nonpositive_one_increment_ae X θ hθ hψ
  rw [ae_iff]
  have e : {ω : Ω | ¬ X.X 1 ω ≤ 0} = {ω : Ω | 0 < X.X 1 ω} := by ext ω; simp
  rw [e]; exact h0
