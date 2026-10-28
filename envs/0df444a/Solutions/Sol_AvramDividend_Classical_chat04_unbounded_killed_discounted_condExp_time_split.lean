-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_killed_discounted_condExp_time_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:31:09.176912+00:00
-- url     : https://prove2.me/submissions/66bbbffb-bb03-4e94-abde-76c23a63949b

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_killed_discounted_condExp_time_split
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-- Split the killed discounted q-scale conditional expectation at a deterministic time
    under unbounded variation, without the additional Standing assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (s : ℝ))) *
          P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
            0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
              (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
                W (x + X.X u ω)) | 𝓕 s] ω) := by
  let B : Set Ω :=
    {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}
  let C : Set Ω :=
    {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u → ¬ X.X v ω < -x}
  have hEq : B = C := by
    ext ω
    change (∀ v : ℝ≥0, s ≤ v → v ≤ u →
      0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)) ↔
      (∀ v : ℝ≥0, s ≤ v → v ≤ u → ¬ X.X v ω < -x)
    constructor
    · intro h v hsv hvu
      have hv := h v hsv hvu
      have hle : -x ≤ X.X v ω := by linarith
      exact not_lt.mpr hle
    · intro h v hsv hvu
      have hv : -x ≤ X.X v ω := not_lt.mp (h v hsv hvu)
      linarith
  have hB : MeasurableSet B := by
    rw [hEq]
    exact chat04_lower_survival_closed_window_measurable
      X (-x) s u hsu
  have hScale : Integrable (fun ω => W (x + X.X u ω)) P :=
    chat04_unbounded_scale_fixed_time_integrable
      X q hq W hW hnbv x u
  have hDiscounted : Integrable
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) P :=
    hScale.const_mul (Real.exp (-(q * ((u : ℝ) - (s : ℝ)))))
  have hInt : Integrable
      (B.indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P :=
    hDiscounted.indicator hB
  exact chat04_killed_discounted_condExp_time_split
    X τ hCover q W x s u hsu hInt
