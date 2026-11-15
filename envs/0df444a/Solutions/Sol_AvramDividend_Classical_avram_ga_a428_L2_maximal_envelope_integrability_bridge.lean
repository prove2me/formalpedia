-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a428_L2_maximal_envelope_integrability_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:19:00.239412+00:00
-- url     : https://prove2.me/submissions/3ea3d45c-1a29-4994-8f55-491ee2a4c480

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a433_real_eLpNorm_two_as_lintegral_square
import Theorems.Thm_AvramDividend_Classical_avram_ga_a436_integral_square_eq_lintegral_nnnorm_square
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f g h : Ω → ℝ)
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hf_nn : ∀ ω, 0 ≤ f ω)
    (hfg : ∀ ω, f ω ≤ (g ω)^2)
    (hh : Integrable (fun ω => (h ω)^2) P)
    (hp : eLpNorm g 2 P ≤ 2 * eLpNorm h 2 P) :
    Integrable f P ∧
      (∫ ω, f ω ∂P) ≤ 4 * (∫ ω, (h ω)^2 ∂P) := by
  classical
  have hp2 := hp
  rw [AvramDividend.Classical.avram_ga_a433_real_eLpNorm_two_as_lintegral_square,
      AvramDividend.Classical.avram_ga_a433_real_eLpNorm_two_as_lintegral_square] at hp2
  have hsquared := ENNReal.rpow_le_rpow hp2 (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _
    (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul] at hsquared
  norm_num at hsquared
  have hhfinite : (∫⁻ ω, (‖h ω‖₊ : ℝ≥0∞)^2 ∂P) < ⊤ := by
    simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, nnnorm_pow] using
      hh.hasFiniteIntegral
  have hgfinite : (∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞)^2 ∂P) < ⊤ := by
    exact lt_of_le_of_lt hsquared
      (ENNReal.mul_lt_top (by norm_num) hhfinite)
  have hgsq : Integrable (fun ω => (g ω)^2) P := by
    refine ⟨(hg.pow 2).aestronglyMeasurable, ?_⟩
    simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, nnnorm_pow] using
      hgfinite
  have hfint : Integrable f P := by
    apply hgsq.mono' hf.aestronglyMeasurable
    filter_upwards with ω
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf_nn ω),
      abs_of_nonneg (sq_nonneg (g ω))] using hfg ω
  constructor
  · exact hfint
  · have hgnorm :=
      AvramDividend.Classical.avram_ga_a436_integral_square_eq_lintegral_nnnorm_square
        g hgsq
    have hhnorm :=
      AvramDividend.Classical.avram_ga_a436_integral_square_eq_lintegral_nnnorm_square
        h hh
    calc
      (∫ ω, f ω ∂P) ≤ ∫ ω, (g ω)^2 ∂P := by
        exact integral_mono_ae hfint hgsq (Filter.Eventually.of_forall hfg)
      _ ≤ 4 * (∫ ω, (h ω)^2 ∂P) := by
        rw [hgnorm, hhnorm]
        have ht := (ENNReal.toReal_le_toReal
          (ne_top_of_lt hgfinite)
          (ENNReal.mul_ne_top (by norm_num) (ne_top_of_lt hhfinite))).mpr hsquared
        simpa [ENNReal.toReal_mul] using ht
