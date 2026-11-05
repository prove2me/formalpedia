-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:30:06.223761+00:00
-- url     : https://prove2.me/submissions/5fe03921-f1f5-4219-b83b-9d27702d1a98

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real Lipschitz and below-cap bounds required by the original stopped
jump theorem are consequences of BV interior C1 and negative-zero extension. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by
  obtain ⟨K, hK⟩ :=
    avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
      X hBV C w hwC1 (a / 2) b (by linarith) hBand
  obtain ⟨R, hR, hW⟩ :=
    avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
      w hwCont hwNeg b (by linarith)
  refine ⟨(K : ℝ), R, K.coe_nonneg, hR, ?_, ?_⟩
  · exact avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
      X hBV C w (fun _ => hwC1) (a / 2) b hOpen hBand K hK
  · intro v hv
    simpa only [Real.norm_eq_abs] using hW v hv
