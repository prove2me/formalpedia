-- Prove2me | solution 7 for AvramDividend.Classical.avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:11:36.447904+00:00
-- url     : https://prove2.me/submissions/1452284d-4c56-49e3-922c-67046f63013e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
import Theorems.Thm_AvramDividend_Classical_avram_a19_single_strict_clock_top_cap_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_bv_finitecap_original_strict_physical_expected_cash_budget
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∃ u : ℕ → ℝ,
      Monotone u ∧
      (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      (∀ n,
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ∂P) ≤ w x) := by
  classical
  intro S
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let u : ℕ → ℝ := fun n => T - δ n
  obtain ⟨hδpos, hδle, hδanti, _⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hTpos
  have hTend : Tendsto u atTop (𝓝 T) := by
    simpa only [u, δ] using
      (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hTpos).2
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact sub_le_sub_left (hδanti hab) T
  · intro n
    exact sub_nonneg.mpr (hδle n)
  · intro n
    exact sub_lt_self T (hδpos n)
  · intro s hs
    have hEv : ∀ᶠ n : ℕ in atTop, s < u n :=
      hTend.eventually (Ioi_mem_nhds hs)
    exact hEv.exists
  · intro n
    by_cases hTop : C = ⊤
    · have hSource :=
        avram_a19_single_strict_clock_top_cap_HJB_source
          X hX hBV q hq w C hC hw_cont hw0 hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD
          hw_nonneg hjump T hT hTpos hTop
          (u n) (sub_nonneg.mpr (hδle n))
          (sub_lt_self T (hδpos n))
      simpa only [u, δ, S] using hSource
    · have hSource :=
        avram_bv_finitecap_original_strict_physical_expected_cash_budget
          X hX hBV q hq w C hC hw_cont hw0 hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
          hjump T hTpos hTop
      simpa only [u, δ, S] using hSource n
