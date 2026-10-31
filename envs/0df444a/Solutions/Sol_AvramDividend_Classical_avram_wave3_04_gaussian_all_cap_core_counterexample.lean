-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_gaussian_all_cap_core_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:58:21.53264+00:00
-- url     : https://prove2.me/submissions/a163f37f-665d-4422-a90e-e1b1e972596f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_cutoff_canonical_analytic_hypotheses
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_core_missing_boundary_counterexample
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_drained_zero_barrier_admissible_any_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original UBV verification core fails at every cap containing the
    initial capital, including every finite such cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (hI : Integrable (X.X 1) P) (hν : X.ν = 0) (hc : X.c = -1)
    (x : ℝ) (hx : 0 < x) (hxle : x ≤ 1)
    (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (T : ℝ) (hT : 0 ≤ T) :
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else z - 1
    let D : ℝ≥0 → Ω → ℝ :=
      fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
    (X.Standing ∧ ¬ X.BoundedVariation ∧
      ContinuousOn w (Ici 0) ∧
      (∀ y : ℝ, y < 0 → w y = 0) ∧
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧
          X.generator w y - (1 : ℝ) * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        1 ≤ deriv w y)) ∧
    IsAdmissibleLe X x C D ∧
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
    X hσ hI hν hc C
  obtain ⟨_, _, _, hnonneg, hjump, hbad⟩ :=
    avram_wave3_04_gaussian_core_missing_boundary_counterexample
      X hσ hI hν hc x hx hxle T hT
  have hDcap := avram_wave3_04_drained_zero_barrier_admissible_any_cap
    X x (le_of_lt hx) C
  exact ⟨hanalytic, hDcap, hnonneg, hjump, hbad⟩
