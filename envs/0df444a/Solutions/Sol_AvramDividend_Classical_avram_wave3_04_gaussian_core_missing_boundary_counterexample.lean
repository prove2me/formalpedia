-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_gaussian_core_missing_boundary_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:26:00.3397+00:00
-- url     : https://prove2.me/submissions/3cde6fb2-3041-4964-88b7-d053c33ef5f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_cutoff_canonical_analytic_hypotheses
import Theorems.Thm_AvramDividend_Classical_drained_strategy_core_pathwise_premises_and_bound_violation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The precise Gaussian counterexample is conditional only on a genuine
    spectrally negative Gaussian Lévy process; every assumption and violation
    of the published UBV core follows from already accepted source lemmas. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (hI : Integrable (X.X 1) P) (hν : X.ν = 0) (hc : X.c = -1)
    (x : ℝ) (hx : 0 < x) (hxle : x ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) :
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
    let D : ℝ≥0 → Ω → ℝ :=
      fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
    (X.Standing ∧ ¬ X.BoundedVariation ∧
      ContinuousOn w (Ici 0) ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ⊤} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < ⊤ →
        X.GeneratorIntegrable w y ∧
          X.generator w y - (1 : ℝ) * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < ⊤ →
        1 ≤ deriv w y)) ∧
    ENNReal.ofReal x ≤ (⊤ : ℝ≥0∞) ∧
    IsAdmissibleLe X x ⊤ D ∧
    (∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) ∧
    ¬ ((∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-((1 : ℝ) * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) := by
  dsimp only
  have hanalytic := gaussian_cutoff_canonical_analytic_hypotheses
    X hσ hI hν hc (⊤ : ℝ≥0∞)
  have haffine :
      ∀ y : ℝ, 0 ≤ y →
        (if y < 0 then (0 : ℝ) else y - 1) = y - 1 := by
    intro y hy
    simp [not_lt.mpr hy]
  have hwx :
      (if x < 0 then (0 : ℝ) else x - 1) ≤ 0 := by
    rw [if_neg (not_lt.mpr (le_of_lt hx))]
    exact sub_nonpos.mpr hxle
  have hcounter := drained_strategy_core_pathwise_premises_and_bound_violation
    X x hx (fun z : ℝ => if z < 0 then 0 else z - 1)
    haffine hwx (1 : ℝ) T hT
  exact ⟨hanalytic, le_top, hcounter⟩
