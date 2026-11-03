-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_positive_cap_complement_positive_time_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:38:34.094609+00:00
-- url     : https://prove2.me/submissions/378074a7-9508-4ecd-bf3d-f40091821fdc

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The nontrivial original BV drift-envelope complement requires strictly
positive horizon and physical drift. The HJB gradient controls the initial
value even at the finite-cap endpoint and at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    w 0 + x ≤ w x ∧ x ≤ w x ∧ 0 < T ∧ 0 < X.drift := by
  have hSec : x - 0 ≤ w x - w 0 := by
    simpa using
      (avram_wave3_03_bv_full_cap_gradient_secant C hC w hw_cont
        hw_smooth hw_grad 0 x (le_refl (0 : ℝ)) hx hxc)
  have hInitial : w 0 + x ≤ w x := by linarith
  have hW : x ≤ w x := by linarith
  have hGap : w x < x + T * X.drift := lt_of_not_ge hEnvelope
  have hProd : 0 < T * X.drift := by linarith
  have hTpos : 0 < T := by
    by_contra hn
    have hT0 : T = 0 := le_antisymm (le_of_not_gt hn) hT
    simp [hT0] at hProd
  have hDriftPos : 0 < X.drift := by
    by_contra hn
    have hDrift : X.drift ≤ 0 := le_of_not_gt hn
    have hNeg : T * X.drift ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hT hDrift
    exact (not_le_of_gt hProd) hNeg
  exact ⟨hInitial, hW, hTpos, hDriftPos⟩
