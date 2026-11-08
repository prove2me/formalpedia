-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_uniformIntegrable_one_of_common_integrable_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:56:47.385931+00:00
-- url     : https://prove2.me/submissions/9d43cce8-eab4-4d91-9703-70d805ed2361

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ι → Ω → ℝ) (G : Ω → ℝ)
    (hGI : Integrable G P)
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (hdom : ∀ i, (fun ω => ‖f i ω‖ₑ) ≤ᵐ[P] (fun ω => ‖G ω‖ₑ)) :
    UniformIntegrable f (1 : ℝ≥0∞) P := by
  have hG : MemLp G (1 : ℝ≥0∞) P := memLp_one_iff_integrable.mpr hGI
  have hC : UniformIntegrable (fun (_ : ι) => G) (1 : ℝ≥0∞) P :=
    uniformIntegrable_const (by norm_num) (by norm_num) hG
  unfold UniformIntegrable at hC ⊢
  refine ⟨hf, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδbound⟩ := hC.2.1 hε
    refine ⟨δ, hδ, ?_⟩
    intro i s hs hms
    have hdom_s :
        (fun ω => ‖s.indicator (f i) ω‖ₑ) ≤ᵐ[P]
          (fun ω => ‖s.indicator G ω‖ₑ) := by
      filter_upwards [hdom i] with ω hω
      by_cases hωs : ω ∈ s
      · simpa [Set.indicator_apply, hωs] using hω
      · simp [Set.indicator_apply, hωs]
    exact (eLpNorm_mono_enorm_ae hdom_s).trans (hδbound i s hs hms)
  ·
    rcases hC.2.2 with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    intro i
    exact (eLpNorm_mono_enorm_ae (hdom i)).trans (hK i)
