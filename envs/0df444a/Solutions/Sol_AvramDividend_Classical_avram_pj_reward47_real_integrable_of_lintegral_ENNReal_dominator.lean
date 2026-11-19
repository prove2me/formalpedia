-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward47_real_integrable_of_lintegral_ENNReal_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:06:43.651205+00:00
-- url     : https://prove2.me/submissions/eb29792e-faa0-4e1f-8195-14523b078956

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : Ω → ℝ≥0∞)
    (hFm : AEMeasurable F P)
    (hFi : (∫⁻ ω, F ω ∂P) < ⊤)
    (g : Ω → ℝ) (hgm : AEStronglyMeasurable g P)
    (K : ℝ) (hK : 0 ≤ K)
    (hDom : ∀ᵐ ω ∂P, |g ω| ≤ K * (F ω).toReal) :
    Integrable g P := by
  have hCount : Integrable (fun ω => (F ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hFm (ne_of_lt hFi)
  have hKCount : Integrable (fun ω => K * (F ω).toReal) P :=
    hCount.const_mul K
  apply hKCount.mono hgm
  filter_upwards [hDom] with ω hω
  have hnonneg : 0 ≤ K * (F ω).toReal :=
    mul_nonneg hK ENNReal.toReal_nonneg
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hω
