-- Prove2me | solution 4 for AvramDividend.Classical.avram_bv_finite734_finite_activity_original_cofinal_prefix_expected_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:24:25.151662+00:00
-- url     : https://prove2.me/submissions/593401e8-ebfb-4041-9f75-c573d6de9987
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_BV_finite_activity_expected_inner_reward_le
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤)
    (hactivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ u : ℕ → ℝ,
      Monotone u ∧
      (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      (∀ n,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
           else 0) ∂P) ≤ w x) := by
  let u : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  have hProfile := avram_a19_uniform_delta_profile T hTpos
  dsimp only at hProfile
  obtain ⟨hPositive, hBound, hAntitone, _hTendstoDelta⟩ := hProfile
  have hLimit := (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
    T hTpos).2
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    change T - T / ((i : ℝ) + 2) ≤ T - T / ((j : ℝ) + 2)
    have h := hAntitone hij
    change T / ((j : ℝ) + 2) ≤ T / ((i : ℝ) + 2) at h
    linarith
  · intro n
    change 0 ≤ T - T / ((n : ℝ) + 2)
    have h := hBound n
    change T / ((n : ℝ) + 2) ≤ T at h
    linarith
  · intro n
    change T - T / ((n : ℝ) + 2) < T
    have h := hPositive n
    change 0 < T / ((n : ℝ) + 2) at h
    linarith
  · intro s hs
    have hEventual := hLimit.eventually (Ioi_mem_nhds hs)
    obtain ⟨n, hn⟩ := hEventual.exists
    exact ⟨n, hn⟩
  · intro n
    have hInner := (avram_bvb_original_BV_finite_activity_expected_inner_reward_le
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos hactivity) n
    simpa only [u] using hInner
