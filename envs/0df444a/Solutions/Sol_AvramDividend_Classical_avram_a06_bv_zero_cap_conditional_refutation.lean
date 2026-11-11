-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_bv_zero_cap_conditional_refutation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:58:53.074943+00:00
-- url     : https://prove2.me/submissions/163d7d13-1a48-409a-bb99-033fa542c50a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact zero-cap admissible barrier has no right jumps, yet its cash
violates the zero verification allowance on a finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D ∧
      (∀ ω (t : ℝ≥0), rightLimit D t ω - D t ω ≤ 0) ∧
      ∃ n : ℕ, (0 : ℝ) ≤ (n : ℝ) ∧
        ¬ ((∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (0 : ℝ)) := by
  obtain ⟨hD, n, hn, hbad⟩ :=
    avram_wave7_09_bv_zero_cap_zero_candidate_finite_horizon_counterexample
      X hX hBV hFinite q hq
  refine ⟨barrierStrategy X 0 0, hD, ?_, n, hn, ?_⟩
  · intro ω t
    have hr := barrierStrategy_no_right_jump_of_initial_below_barrier
      X 0 0 (le_refl (0 : ℝ)) ω t
    rw [hr]
    simp
  · simpa using hbad
