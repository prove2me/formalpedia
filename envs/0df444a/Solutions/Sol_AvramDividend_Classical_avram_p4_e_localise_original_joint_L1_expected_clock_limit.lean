-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_expected_clock_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:34:36.955936+00:00
-- url     : https://prove2.me/submissions/d095190e-fee2-405a-80b1-1278bd90e777

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_explicit_uniform_clock_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Genuine joint L¹ and original measurability give finite expected pre-ruin physical drift limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P))
    (hFiniteMeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω => ∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ) P)
    (hFullMeas : AEStronglyMeasurable (fun ω => (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ)) P) :
    Integrable (fun ω => (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ)) P ∧
    Tendsto (fun n : ℕ => ∫ ω, ∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ ∂P)
      atTop (nhds (∫ ω, (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ) ∂P)) := by
  let B : Ω → ℝ := fun ω => (∫ t : ℝ≥0, ‖f (t, ω)‖ ∂μ)
  let Fn : ℕ → Ω → ℝ := fun n ω => ∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ
  let F : Ω → ℝ := fun ω => (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ)
  have hEnvelope :=
    avram_p4_e_localise_original_joint_L1_explicit_uniform_clock_envelope
      P X x C D hD μ f hf
  have hAE :=
    avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
      P X x C D hD μ f hf
  have hFInt : Integrable F P := by
    apply Integrable.mono hEnvelope.1 hFullMeas
    filter_upwards [hEnvelope.2] with ω hω
    exact (hω.2).trans (le_abs_self (B ω))
  have hBound : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖Fn n ω‖ ≤ B ω := by
    intro n
    filter_upwards [hEnvelope.2] with ω hω
    exact hω.1 n
  have hConv :=
    tendsto_integral_of_dominated_convergence B
      hFiniteMeas hEnvelope.1 hBound hAE
  exact ⟨hFInt, hConv⟩
