-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb29_original_finite_mark_step_measurable_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:18:17.647197+00:00
-- url     : https://prove2.me/submissions/372e5c3e-f2b8-43d4-b54c-080c9f1e2353

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb30_original_finite_mark_floor_uniform_signed_bound
import Theorems.Thm_AvramDividend_Classical_avram_bvb31_original_finite_mark_floor_and_clock_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
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
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (hMassPos : 0 < X.ν (Iio (0 : ℝ))) (hKernel : ∀ s : Set ℝ, IsCompact s →
      s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} →
      UniformContinuousOn
        (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s)
    (ω : Ω) (hRuinNonzero : ruinTime X x D ω ≠ 0)
    (hSource : ∀ r : ℝ≥0, r ≤ (⟨T, le_of_lt hT⟩ : ℝ≥0) →
      X.X r ω = (r : ℝ) * X.drift) :
    let U : ℝ≥0 → ℝ := fun t =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    let rate : ℝ≥0 → ℝ := fun t =>
      Real.exp (-(q * (t : ℝ))) * ψ (U t)
    let μ : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal
    let F : ℕ → ℝ → ℝ := fun n r =>
      if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
        let i : ℕ := ⌊(r / T) * ((n : ℝ) + 2)⌋₊
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
           0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
        then rate (u n i) else 0
      else 0
    let G : ℕ → ℝ → ℝ := fun n r =>
      let t : ℝ≥0 := Real.toNNReal r
      if 0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then rate t else 0
    let μreal : Measure ℝ := (volume : Measure ℝ).restrict (Icc 0 T)
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ n, AEStronglyMeasurable (F n) μreal) ∧
      (∀ n, AEStronglyMeasurable (G n) μreal) ∧
      (∀ n, ∀ᵐ r ∂μreal, ‖F n r‖ ≤ B) ∧
      (∀ n, ∀ᵐ r ∂μreal, ‖G n r‖ ≤ B) ∧
      (∀ n, AEStronglyMeasurable
        (fun t : ℝ≥0 =>
          if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
             (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
             0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
          then rate t else 0) μ) := by
  intro U ψ rate μ F G μreal
  obtain ⟨B, hB, hF, hG⟩ :=
    avram_bvb30_original_finite_mark_floor_uniform_signed_bound
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x hx hxc D hD T hT u hgrid hmono huniform hFinite hActivity
      hMassPos hKernel ω hRuinNonzero hSource
  obtain ⟨hFM, hGM, hJM⟩ :=
    avram_bvb31_original_finite_mark_floor_and_clock_measurable
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x hx hxc D hD T hT u hgrid hmono huniform hFinite hActivity
      hMassPos hKernel ω hRuinNonzero hSource
  refine ⟨B, hB, hFM, hGM, ?_, ?_, hJM⟩
  · intro n
    exact Filter.Eventually.of_forall (hF n)
  · intro n
    exact Filter.Eventually.of_forall (hG n)
