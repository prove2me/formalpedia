-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:02:15.375849+00:00
-- url     : https://prove2.me/submissions/6377e4a2-e2a4-4a29-83be-8c76ca6fbde5

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_physical_integral_DCT
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original physical stopped integrals converge a.s. under genuine joint L¹. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P)) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ => ∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ)
        atTop
        (nhds (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ)) := by
  have hFibre := hf.prod_left_ae
  filter_upwards [hFibre] with ω hω
  exact avram_p4_e_localise_original_true_clock_physical_integral_DCT
    X x C D hD ω μ (fun t => f (t, ω)) hω
