-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_full_ruin_G_integrable_and_nonpos_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:48:04.3879+00:00
-- url     : https://prove2.me/submissions/9ba1f7c1-f14e-4bb8-b6b1-3461de355ee4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_clock_product_measurable_sets
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_limit_preserves_nonpositive_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The exact original full ruin physical residual is globally L¹ and has nonpositive mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P))
    (hNonpos : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0, ({s : ℝ≥0 |
        (s : ℝ≥0∞) < min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
          (fun t => f (t, ω)) t ∂μ) ≤ 0) :
    Integrable (fun ω => ∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
          (fun t => f (t, ω)) t ∂μ) P ∧
    (∫ ω, ∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
          (fun t => f (t, ω)) t ∂μ ∂P) ≤ 0 := by
  have hSets :=
    avram_p4_e_localise_original_ruin_clock_product_measurable_sets
      X x D hDiv
  have hProd : Integrable
      (({p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) < ruinTime X x D p.2}).indicator f)
      (μ.prod P) := hf.indicator hSets.1
  have hFull : Integrable (fun ω => ∫ t : ℝ≥0,
      ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
        (fun t => f (t, ω)) t ∂μ) P := by
    exact hProd.integral_prod_right
  have hSign :=
    avram_p4_e_localise_original_joint_L1_limit_preserves_nonpositive_drift
      P X x C D hD μ f hf hNonpos
  exact ⟨hFull, integral_nonpos_of_ae hSign⟩