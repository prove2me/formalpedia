-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_ruin_truncated_terminal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:24:37.157868+00:00
-- url     : https://prove2.me/submissions/718f84d2-6b5e-4520-8a09-c81530f959da

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

/-- Original BV strict preterminal L1 survives the exact bounded ruin
clock at every deterministic S strictly before its horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hfinite : IsFiniteMeasure P)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (T S : ℝ≥0) (hST : S < T) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) <
          (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)
      then Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) P := by
  have hBase :=
    avram_p3_bv_original_strict_preterminal_L1
      X hBV hXzero hfinite x D hD.1.1 w hw_cont hw_neg q S
  have hEvent (ω : Ω) :
      ((S : ℝ≥0∞) <
          (((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0∞)) ↔
        (S : ℝ≥0∞) < ruinTime X x D ω := by
    have hClock :=
      (avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
        X x D T).1 ω S
    exact hClock.trans (by simp [hST])
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
