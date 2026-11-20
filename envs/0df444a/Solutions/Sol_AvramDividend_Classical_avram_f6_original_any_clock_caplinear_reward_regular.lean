-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_any_clock_caplinear_reward_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T16:11:49.132892+00:00
-- url     : https://prove2.me/submissions/469f71d1-355b-4c96-82d9-970f9e15519a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_real_caplinear_cash_exact
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_source_reward_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (c : Ω → ℝ≥0)
    (hc : IsStoppingTime 𝓕.rightCont
      (fun ω => (c ω : WithTop ℝ≥0))) :
    let V : ℝ → ℝ := fun z =>
      if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal)
    let R : Ω → ℝ := fun ω =>
      Real.exp (-(q * (c ω : ℝ))) *
        V (if c ω = 0 ∨ (c ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (c ω) ω - rightLimit D (c ω) ω
          else riskProcess X x D (c ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (c ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    Measurable R ∧ (∀ ω, 0 ≤ R ω) := by
  dsimp only
  let V : ℝ → ℝ := fun z =>
    if ENNReal.ofReal z ≤ C then w z
    else w C.toReal + (z - C.toReal)
  let Q : Ω → ℝ := fun ω =>
    Real.exp (-(q * (c ω : ℝ))) *
      w (if c ω = 0 ∨ (c ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (c ω) ω - rightLimit D (c ω) ω
        else riskProcess X x D (c ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (c ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  let R : Ω → ℝ := fun ω =>
    Real.exp (-(q * (c ω : ℝ))) *
      V (if c ω = 0 ∨ (c ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (c ω) ω - rightLimit D (c ω) ω
        else riskProcess X x D (c ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (c ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  change Measurable R ∧ (∀ ω, 0 ≤ R ω)
  have hV (z : ℝ) : V z =
      (if C = ⊤ then w z else if z ≤ C.toReal then w z
       else w C.toReal + (z - C.toReal)) := by
    by_cases ht : C = ⊤
    · simp [V, ht]
    · simp [V, ht, ENNReal.ofReal_le_iff_le_toReal ht]
  have hEq : R = Q := by
    funext ω
    have hs := avram_f6_original_stopped_reward_real_caplinear_cash_exact
      X x C hC hxc w D hD q (fun _ => c) (fun _ => Q)
      (by intro j η; rfl) 0 ω
    dsimp only at hs
    simpa only [R, hV] using hs.symm
  rw [hEq]
  exact ⟨avram_ubv_top9_original_any_clock_source_reward_measurable
    X x q w hw_cont hw_neg D hD.1.1 c hc Q (by intro ω; rfl),
    avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q c Q (by intro ω; rfl)⟩
