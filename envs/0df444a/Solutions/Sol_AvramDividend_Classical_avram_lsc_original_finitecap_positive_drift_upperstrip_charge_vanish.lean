-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_original_finitecap_positive_drift_upperstrip_charge_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:12:48.032735+00:00
-- url     : https://prove2.me/submissions/90076d41-5cb7-4286-9496-c3c2638618b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_admissible_upperstrip_expected_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine positive Gaussian drift contribution from the upper-cap
occupation vanishes as the upper localisation band tends to the cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    Tendsto
      (fun j : ℕ => max X.c 0 *
        (∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
              riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume ∂P))
      atTop (𝓝 (0 : ℝ)) := by
  have hOcc :=
    avram_f6_original_finitecap_admissible_upperstrip_expected_zero
      X hBV x C hC hFinite hxc D hD n hn
  simpa only [mul_zero] using hOcc.const_mul (max X.c 0)

