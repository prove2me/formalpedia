-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_BV_ruin_truncated_terminal_L1_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:24:41.756657+00:00
-- url     : https://prove2.me/submissions/a6175aa5-73ea-460d-99ce-978f6fc9c335

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual bounded ruin-clock original BV strict terminal payoff
is L1 at every deterministic time, including and after the horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hfinite : IsFiniteMeasure P)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (T S : ℝ≥0) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) <
          (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)
      then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) P := by
  have hClock := 
    (avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
      X x D T).1
  by_cases hST : S < T
  · have hBase :=
      avram_p3_bv_original_strict_preterminal_L1
        X hBV hXzero hfinite x D hD.1.1 w hw_cont hw_neg q S
    have hEvent (ω : Ω) :
        ((S : ℝ≥0∞) <
          (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)) ↔
        (S : ℝ≥0∞) < ruinTime X x D ω := by
      exact (hClock ω S).trans (by simp [hST])
    have hFun :
        (fun ω : Ω =>
          if (S : ℝ≥0∞) <
            (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)
          then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
          else 0) =
        (fun ω : Ω =>
          if (S : ℝ≥0∞) < ruinTime X x D ω
          then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
          else 0) := by
      funext ω
      simpa only [hEvent ω]
    rw [hFun]
    exact hBase
  · have hTS : T ≤ S := le_of_not_gt hST
    have hFalse (ω : Ω) :
        ¬ ((S : ℝ≥0∞) <
          (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)) := by
      intro h
      exact (not_lt_of_ge hTS) ((hClock ω S).mp h).2
    have hFun :
        (fun ω : Ω =>
          if (S : ℝ≥0∞) <
            (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)
          then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
          else 0) = (fun _ : Ω => (0 : ℝ)) := by
      funext ω
      exact if_neg (hFalse ω)
    rw [hFun]
    haveI : IsFiniteMeasure P := hfinite
    exact integrable_const (0 : ℝ)
