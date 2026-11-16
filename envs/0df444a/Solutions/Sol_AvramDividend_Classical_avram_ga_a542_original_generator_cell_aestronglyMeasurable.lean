-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a542_original_generator_cell_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:40:22.684049+00:00
-- url     : https://prove2.me/submissions/ab60986d-bf75-43b9-a2b8-2b663cdd1364

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a556_stopped_strict_future_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a546_zerojump_generator_positive_interior_measurable_extension
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
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      if 0 < ρ ω ∧ s < ρ ω then
        (Δ : ℝ) * E s * X.generator w (Y s)
      else 0
    ∀ m i : ℕ, i < m →
      AEStronglyMeasurable (G m i) P := by
  classical
  intro G m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let Y : Ω → ℝ := fun ω =>
    x + X.X s ω - rightLimit D s ω
  have hXm : Measurable[𝓕.rightCont s] (X.X s) :=
    (X.adapted s).mono (𝓕.le_rightCont s) le_rfl
  have hDm : Measurable[𝓕.rightCont s] (rightLimit D s) :=
    (dividendStrategy_rightLimit_adapted_rightCont D hD.1.1) s
  have hY_meas : Measurable Y :=
    ((measurable_const.add hXm).sub hDm).mono
      (𝓕.rightCont.le s) le_rfl
  have hMask : MeasurableSet {ω : Ω | s < ρ ω} :=
    avram_ga_a556_stopped_strict_future_event_measurable 𝓕 ρ hρstop s
  have hBand :=
    avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
      X x D hD.1.1 ρ j hprefix
  have hGenMeas :=
    avram_ga_a546_zerojump_generator_positive_interior_measurable_extension
      X hNuZero w C hw_smooth
  let H : Ω → ℝ := fun ω =>
    if s < ρ ω then (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
      (if 0 < Y ω ∧ ENNReal.ofReal (Y ω) < C then
        X.generator w (Y ω) else 0)
    else 0
  have hH : Measurable H := by
    dsimp [H]
    exact Measurable.ite hMask
      (measurable_const.mul (hGenMeas.comp hY_meas))
      measurable_const
  have hEq : G m i =ᵐ[P] H := by
    filter_upwards [hBand] with ω hb
    by_cases hs : s < ρ ω
    · have hr : 0 < ρ ω := lt_of_le_of_lt bot_le hs
      have hpos : 0 < Y ω := by
        have hl := (hb s hs).1
        exact lt_of_lt_of_le
          (by positivity : 0 < (1 : ℝ) / ((j : ℝ) + 1)) hl
      have hcap : ENNReal.ofReal (Y ω) < C := by simp [hTopCap]
      have hh : 0 < ρ ω ∧
          (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω :=
        ⟨hr, by simpa only [s, Δ] using hs⟩
      change (if 0 < ρ ω ∧ s < ρ ω then
        (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) * X.generator w (Y ω) else 0) =
        (if s < ρ ω then (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
          (if 0 < Y ω ∧ ENNReal.ofReal (Y ω) < C then X.generator w (Y ω)
            else 0) else 0)
      have hh : 0 < ρ ω ∧ s < ρ ω := ⟨hr, hs⟩
      have hp : 0 < Y ω ∧ ENNReal.ofReal (Y ω) < C := ⟨hpos, hcap⟩
      simp only [if_pos hh, if_pos hs, if_pos hp]
    · have hn : ¬(0 < ρ ω ∧ s < ρ ω) := fun h => hs h.2
      simp [G, H, s, Δ, hs, hn]
  exact hH.aestronglyMeasurable.congr hEq.symm
