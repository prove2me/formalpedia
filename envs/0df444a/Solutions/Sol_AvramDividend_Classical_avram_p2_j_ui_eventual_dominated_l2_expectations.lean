-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_eventual_dominated_l2_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:26:10.634203+00:00
-- url     : https://prove2.me/submissions/ebec22e2-927d-4f26-8a6c-13c4b710ec9c

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_squared_enorm_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_l2_ae_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! A signed real sequence inherits eventual L² control from source ENNReal envelopes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (G : ℕ → Ω → ENNReal)
    (B : ℝ≥0) (N : ℕ)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Y n ω‖ₑ ≤ G n ω)
    (hB : ∀ n, N ≤ n →
      (∫⁻ ω, (G n ω) ^ (2 : ℝ) ∂P) ≤ (B : ENNReal) ^ 2)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  have hLp : ∀ n, N ≤ n → eLpNorm (Y n) 2 P ≤ (B : ENNReal) := by
    intro n hn
    apply avram_p2_j_ui_lintegral_squared_enorm_bound P (Y n) B
    have hpow : ∀ᵐ ω ∂P,
        ‖Y n ω‖ₑ ^ (2 : ℝ) ≤ (G n ω) ^ (2 : ℝ) := by
      filter_upwards [hdom n] with ω hω
      gcongr <;> exact hω
    exact (lintegral_mono_ae hpow).trans (hB n hn)
  exact avram_p2_j_ui_eventual_l2_ae_expectations
    P Y Z B N hm hLp hae
