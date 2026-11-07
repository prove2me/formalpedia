-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_masked_reward_dominates_exact_F
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:42:00.879831+00:00
-- url     : https://prove2.me/submissions/ec4904ab-cfdf-4a34-b6ed-974c6986cb41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original closed-cash reward is pointwise bounded by the
    zero-clock-masked Ito reward used in the signed source certificate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (k : ℕ) (ω : Ω) :
    F k ω ≤ (if σ k ω = 0 then w x else F k ω) := by
  classical
  by_cases hzero : σ k ω = 0
  · simpa [hzero] using
      (avram_ubv_loc6_original_zero_clock_exact_physical_F_le
        X x q w C D hD hjump σ F hFsource k ω hzero)
  · simp [hzero]
