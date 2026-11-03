-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_strict_drift_envelope_complement_positive_clock_and_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:36:24.218169+00:00
-- url     : https://prove2.me/submissions/8556b712-841a-4f4c-8175-ebd0cf23a612

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- In the exact canonical BV strict drift-envelope complement branch, the horizon and original Lévy drift must both be strictly positive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    0 < T ∧ 0 < X.drift := by
  have hStep :
      x - 0 ≤ w x - w 0 :=
    avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
      C hC w hw_cont hw_smooth hw_grad
      x hx hxc
      0 ⟨le_refl (0 : ℝ), hx⟩
      x ⟨hx, le_refl x⟩ hx
  have hValueFloor : x ≤ w x := by
    linarith only [hStep, hw0]
  have hStrict : w x < x + T * X.drift :=
    lt_of_not_ge hEnvelope
  have hProd : 0 < T * X.drift := by
    linarith only [hValueFloor, hStrict]
  have hTpos : 0 < T := by
    by_contra hnot
    have hZero : T = 0 :=
      le_antisymm (le_of_not_gt hnot) hT
    simp [hZero] at hProd
  have hDriftPos : 0 < X.drift := by
    by_contra hnot
    have hDriftNonpos : X.drift ≤ 0 := le_of_not_gt hnot
    have hProdNonpos : T * X.drift ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hT hDriftNonpos
    exact (not_le_of_gt hProd) hProdNonpos
  exact ⟨hTpos, hDriftPos⟩
