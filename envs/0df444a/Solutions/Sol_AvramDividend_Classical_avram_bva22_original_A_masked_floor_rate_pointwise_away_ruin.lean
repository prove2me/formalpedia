-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva22_original_A_masked_floor_rate_pointwise_away_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:52:00.122522+00:00
-- url     : https://prove2.me/submissions/2cc419d1-c82a-4cf9-a9c2-1eb4d6200e82

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_preruin_masked_uniform_floor_kernel_converges
import Theorems.Thm_AvramDividend_Classical_avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original closed-cap A-grid kernel converges at every positive non-ruin time. -/
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
    (q T : ℝ) (hT : 0 < T) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    let F : ℝ≥0 → ℝ := fun r => Real.exp (-(q * (r : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν
    Tendsto (fun n =>
      if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C then F (s n) else 0)
      atTop (𝓝 (if (t : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then F t else 0)) := by
  intro s U F
  rcases lt_or_gt_of_ne hNotRuin with hpre | hpost
  · have hcap : 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C := by
      simpa [U] using
        avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
          X x C hxc D hD ω t (Or.inr hpre)
    have hPre : Tendsto (fun n =>
        if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
           0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C
        then F (s n) else 0) atTop (𝓝 (F t)) := by
      exact avram_bva20_original_preruin_masked_uniform_floor_kernel_converges
        X hX hBV x C hxc D hD ω S t ht htpos hpre hsource hFinite
        w hw_cont hw_neg hActivity q T hT
    have hTarget :
        (if (t : ℝ≥0∞) < ruinTime X x D ω ∧
           0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then F t else 0) = F t := by
      simp [hpre, hcap]
    rw [hTarget]
    exact hPre
  · have hsPost : ∀ᶠ n : ℕ in atTop,
        ¬ ((s n : ℝ≥0∞) < ruinTime X x D ω) := by
      simpa [s] using
        (avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
          T hT t (ruinTime X x D ω) hpost)
    have hEventually : ∀ᶠ n : ℕ in atTop,
        (if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
           0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C
         then F (s n) else 0) = 0 := by
      filter_upwards [hsPost] with n hn
      simp [hn]
    have hNotPre : ¬ ((t : ℝ≥0∞) < ruinTime X x D ω) :=
      not_lt.mpr hpost.le
    have hTarget :
        (if (t : ℝ≥0∞) < ruinTime X x D ω ∧
           0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then F t else 0) = 0 := by
      simp [hNotPre]
    rw [hTarget]
    exact (tendsto_congr' hEventually).2 tendsto_const_nhds
