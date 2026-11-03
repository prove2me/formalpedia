-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_ennreal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:52:13.829467+00:00
-- url     : https://prove2.me/submissions/22d044b4-bb91-4808-8a3e-b188ab67ca57

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_signed_stieltjes_expected_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Uniform genuine original signed budgets at deterministic
    integer horizons control full ENNReal cash at every finite random clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hDetBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
  have hMinBudget (n : ℕ) :
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by
    let θ : Ω → ℝ≥0 := fun ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0))
    let κ : Ω → ℝ≥0 := fun _ => (((n + 1 : ℕ) : ℝ≥0))
    have hθBound (ω : Ω) : θ ω ≤ (((n + 1 : ℕ) : ℝ≥0)) :=
      min_le_right _ _
    have hκBound (ω : Ω) : κ ω ≤ (((n + 1 : ℕ) : ℝ≥0)) := le_rfl
    have hθMeas : Measurable (fun ω => (θ ω : ℝ)) := by
      have hEq : (fun ω => (θ ω : ℝ)) =
          (fun ω => min (τ ω : ℝ) (((n + 1 : ℕ) : ℝ))) := by
        funext ω
        simp only [θ, NNReal.coe_min, NNReal.coe_natCast]
      rw [hEq]
      exact hτMeas.min measurable_const
    have hMono :=
      avram_wave7_03_original_bounded_random_clock_signed_stieltjes_expected_monotone
        X x C D hD q hq (((n + 1 : ℕ) : ℝ≥0))
        θ κ hθBound hκBound hθMeas measurable_const hθBound
    have hDet : (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (κ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by
      simpa only [κ, NNReal.coe_natCast] using hDetBudget n
    exact hMono.trans hDet
  exact avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
    X x C D hD q hq τ hτMeas B hMinBudget
