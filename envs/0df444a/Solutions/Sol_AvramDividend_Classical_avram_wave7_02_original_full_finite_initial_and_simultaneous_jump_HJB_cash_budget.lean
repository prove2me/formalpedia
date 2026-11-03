-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_full_finite_initial_and_simultaneous_jump_HJB_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:19:20.936271+00:00
-- url     : https://prove2.me/submissions/75cc76e3-ad97-425d-9d12-44c1a61ba45b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_plus_positive_clock_finite_all_atomic_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_prejump_valid_finite_source_mark_discounted_C1_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- The true original time-zero right Stieltjes atom and all selected
positive pre-ruin concurrent source/dividend jumps have a complete finite
pathwise HJB payment budget under source pre-reserve cap and negativity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v < 0, w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : Finset ℝ≥0)
    (hTimes : ∀ t ∈ S, 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hValid : ∀ t ∈ S,
      X.X t ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∧
      0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω ∧
      ENNReal.ofReal
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C) :
    (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∑ t ∈ S,
        (Real.exp (-(q * (t : ℝ))) *
          ((w (x + X.X t ω - rightLimit D t ω) -
              w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
                D t ω)) +
            (rightLimit D t ω - D t ω)))) ≤ w x := by
  have hAtomic :=
    avram_wave7_02_original_initial_plus_positive_clock_finite_all_atomic_source_budget
      X x q D hD w hjump ω S hTimes
  have hSource :=
    avram_wave7_02_original_prejump_valid_finite_source_mark_discounted_C1_nonpositive
      X C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
      x D ω q S hValid
  linarith only [hAtomic, hSource]
