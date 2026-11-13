-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b23_original_A_K_common_pointwise_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:22:54.017699+00:00
-- url     : https://prove2.me/submissions/f3aa2a32-999b-45a0-8c31-ca00894a14aa

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_A_masked_floor_rate_pointwise_away_ruin
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_K_inner_horizon_masked_rate_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_b20_bvb23_real_index_terminal_indicator_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hNotRuin : (t : ℝ≥0∞) ≠ ruinTime X x D ω)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) (hT : 0 < T) (htT : (t : ℝ) < T) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    let F : ℝ≥0 → ℝ := fun r => Real.exp (-(q * (r : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν
    (Tendsto (fun n =>
      if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C then F (s n) else 0)
      atTop (𝓝 (if (t : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then F t else 0))) ∧
    Tendsto (fun n =>
      if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then F t else 0)
      atTop (𝓝 (if (t : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then F t else 0)) := by
  dsimp only
  constructor
  · exact avram_bva22_original_A_masked_floor_rate_pointwise_away_ruin
      X hX hBV x C hxc D hD ω S t ht htpos hNotRuin hsource hFinite
      w hw_cont hw_neg hActivity q T hT
  · exact avram_b20_bvb23_real_index_terminal_indicator_tendsto
      T hT (ruinTime X x D ω) t htpos htT hNotRuin
      C
      (Function.leftLim
        (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) t)
      (Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ),
          w (Function.leftLim (fun r : ℝ≥0 =>
            x + X.X r ω - rightLimit D r ω) t + z) -
          w (Function.leftLim (fun r : ℝ≥0 =>
            x + X.X r ω - rightLimit D r ω) t) ∂X.ν)
