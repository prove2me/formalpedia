-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_explicit_uniform_clock_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:16:00.87027+00:00
-- url     : https://prove2.me/submissions/b4b64ec6-9298-4345-8593-52173032b51a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Genuine joint L¹ supplies a single integrable source-clock envelope for every horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P)) :
    Integrable (fun ω => (∫ t : ℝ≥0, ‖f (t, ω)‖ ∂μ)) P ∧
    ∀ᵐ ω ∂P,
      (∀ n : ℕ, ‖(∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
          (fun t => f (t, ω)) t ∂μ)‖ ≤ (∫ t : ℝ≥0, ‖f (t, ω)‖ ∂μ)) ∧
      ‖(∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
          (fun t => f (t, ω)) t ∂μ)‖ ≤ (∫ t : ℝ≥0, ‖f (t, ω)‖ ∂μ) := by
  have hEnvelope : Integrable (fun ω => (∫ t : ℝ≥0, ‖f (t, ω)‖ ∂μ)) P :=
    hf.integral_norm_prod_right
  have hFibres : ∀ᵐ ω ∂P, Integrable (fun t => f (t, ω)) μ :=
    hf.prod_left_ae
  refine ⟨hEnvelope, ?_⟩
  filter_upwards [hFibres] with ω hω
  have hBound (S : Set ℝ≥0) :
      ‖∫ t : ℝ≥0, S.indicator (fun t => f (t, ω)) t ∂μ‖ ≤
        (∫ t : ℝ≥0, ‖f (t, ω)‖ ∂μ) := by
    apply norm_integral_le_of_norm_le hω.norm
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t ∈ S
    · simp [Set.indicator, ht]
    · simp [Set.indicator, ht]
  exact ⟨fun n => hBound {s : ℝ≥0 | (s : ℝ≥0∞) <
      min (ruinTime X x D ω) (n : ℝ≥0∞)},
    hBound {s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}⟩
