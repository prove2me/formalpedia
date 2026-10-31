-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_gaussian_finite_cap_core_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:40:45.016971+00:00
-- url     : https://prove2.me/submissions/902df7f9-6176-4514-9dbe-6c4ba0e2c204

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_gaussian_cutoff_canonical_analytic_hypotheses
import Theorems.Thm_AvramDividend_Classical_drained_strategy_core_pathwise_premises_and_bound_violation
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_reserve_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The full Gaussian UBV verification premises fail to imply the reward bound
    even with a finite reserve cap equal to one. -/
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
      ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ)} ∧
      (∀ y : ℝ, 0 < y →
        ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ) →
        X.GeneratorIntegrable w y ∧
          X.generator w y - (1 : ℝ) * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y →
        ENNReal.ofReal y < ENNReal.ofReal (1 : ℝ) →
        1 ≤ deriv w y)) ∧
    ENNReal.ofReal x ≤ ENNReal.ofReal (1 : ℝ) ∧
    IsAdmissibleLe X x (ENNReal.ofReal (1 : ℝ)) D ∧
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
    X hσ hI hν hc (ENNReal.ofReal (1 : ℝ))
  have haffine :
      ∀ y : ℝ, 0 ≤ y →
        (if y < 0 then (0 : ℝ) else y - 1) = y - 1 := by
    intro y hy
    simp [not_lt.mpr hy]
  have hwx :
      (if x < 0 then (0 : ℝ) else x - 1) ≤ 0 := by
    rw [if_neg (not_lt.mpr (le_of_lt hx))]
    exact sub_nonpos.mpr hxle
  obtain ⟨hDtop, hnonneg, hjump, hbad⟩ :=
    drained_strategy_core_pathwise_premises_and_bound_violation
      X x hx (fun z : ℝ => if z < 0 then 0 else z - 1)
      haffine hwx (1 : ℝ) T hT
  have hDcap : IsAdmissibleLe X x (ENNReal.ofReal (1 : ℝ))
      (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) := by
    rcases hDtop with ⟨hD, _⟩
    refine ⟨hD, ?_⟩
    intro ω t ht
    have hneg := barrierStrategy_plus_linear_drain_reserve_negative
      X x (le_of_lt hx) ω t ht
    rw [ENNReal.ofReal_eq_zero.mpr (le_of_lt hneg)]
    exact bot_le
  have hcap : ENNReal.ofReal x ≤ ENNReal.ofReal (1 : ℝ) :=
    ENNReal.ofReal_le_ofReal hxle
  exact ⟨hanalytic, hcap, hDcap, hnonneg, hjump, hbad⟩
