-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_strict_ruin_terminal_integral_zero_after_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:24:24.748226+00:00
-- url     : https://prove2.me/submissions/5c890ca0-6f2c-46ff-bc6f-78ed9df71adf

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At or beyond the deterministic horizon the original strict
ruin-stopped terminal payoff integral is identically zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (T S : ℝ≥0) (hTS : T ≤ S) :
    (∫ ω, if (S : ℝ≥0∞) <
        (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)
      then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0 ∂P) = 0 := by
  have hClock :=
    (avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
      X x D T).1
  have hFalse (ω : Ω) :
      ¬ ((S : ℝ≥0∞) <
        (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)) := by
    intro h
    have hSltT : S < T := ((hClock ω S).mp h).2
    exact (not_lt_of_ge hTS) hSltT
  have hFun :
      (fun ω : Ω =>
        if (S : ℝ≥0∞) <
          (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)
        then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
        else 0) = (fun _ : Ω => (0 : ℝ)) := by
    funext ω
    exact if_neg (hFalse ω)
  rw [hFun]
  simp
