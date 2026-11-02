-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_canonical_hjump_ae_diffuse_full_stieltjes_control_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:55:09.69403+00:00
-- url     : https://prove2.me/submissions/866109d6-5876-4161-8005-2e8863751892

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_countable_chronological_signed_correction_nonpos_of_summable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original controlled full signed Stieltjes correction is nonpositive
with diffuse interior localisation only ν-a.e.; the time-zero and cap-contact
right atoms use the genuine admissible closed-cap secant instead. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ≥0) (hA : A.Countable)
    (hAT : ∀ t : A, (t : ℝ≥0) ≤ T)
    (hAP : ∀ t : A, ((t : ℝ≥0) : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hlocAe : ∀ᵐ s ∂ν.restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
      0 < riskProcess X x D s.toNNReal ω ∧
        ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (hIntegrable : IntegrableOn
      (fun s : ℝ => Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) ν)
    (hSummable : Summable (fun t : A =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) +
    (∑' t : A,
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by
  apply add_nonpos
  · have hAe :
        ∀ᵐ s ∂ν.restrict
          (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
        Real.exp (-q * s) *
            (1 - deriv w (riskProcess X x D s.toNNReal ω)) ≤ 0 := by
      filter_upwards [hlocAe] with s hs
      have hg := hw_grad (riskProcess X x D s.toNNReal ω) hs.1 hs.2
      exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (Real.exp_pos _)) (by linarith)
    change (∫ s : ℝ,
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω))
      ∂ν.restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ))) ≤ 0
    exact integral_nonpos_of_ae hAe
  · have hjumpAt : ∀ t : ℝ≥0, t ≤ T →
        (t : ℝ) ∈ paymentTimes (ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω)) := by
      intro t _ hp
      apply hjump ω t
      change 0 ≤ (t : ℝ) ∧
        ((t : ℝ) = 0 ∨ ENNReal.ofReal (t : ℝ) <
          ruinTime X x D ω) at hp
      rcases hp.2 with hzero | hbefore
      · left
        exact_mod_cast hzero
      · right
        simpa using hbefore
    exact avram_wave4_04b_countable_chronological_signed_correction_nonpos_of_summable
      X x D hD w ω T (ruinTime X x D ω) q
      A hA hAT hAP hjumpAt hSummable