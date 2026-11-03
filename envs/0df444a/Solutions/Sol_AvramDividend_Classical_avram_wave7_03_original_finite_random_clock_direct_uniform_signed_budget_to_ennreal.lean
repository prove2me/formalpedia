-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:06:58.244102+00:00
-- url     : https://prove2.me/submissions/d9afcc48-a6c3-46b2-a4ad-5cd2ce92b180

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_outer_cash_eq_iSup_bounded_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Any uniform expected signed Stieltjes budget for the bounded
    truncations controls the full original finite random-clock ENNReal cash. -/
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
    (hBound : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  rw [avram_wave7_03_original_finite_random_clock_outer_cash_eq_iSup_bounded_cash
    X x D hDiv q τ hτMeas]
  apply iSup_le
  intro n
  let θ : Ω → ℝ≥0 := fun ω => min (τ ω) (((n + 1 : ℕ) : ℝ≥0))
  have hθMeas : Measurable (fun ω => (θ ω : ℝ)) := by
    have hEq : (fun ω => (θ ω : ℝ)) =
        (fun ω => min (τ ω : ℝ) (((n + 1 : ℕ) : ℝ))) := by
      funext ω
      simp only [θ, NNReal.coe_min, NNReal.coe_natCast]
    rw [hEq]
    exact hτMeas.min measurable_const
  have hθBound (ω : Ω) : θ ω ≤ (((n + 1 : ℕ) : ℝ≥0)) :=
    min_le_right _ _
  calc
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
      ENNReal.ofReal
        (∫ ω, (∫ t in
            paymentTimes (ruinTime X x D ω) ∩
              Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) :=
            (avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
              X x C D hD q hq (((n + 1 : ℕ) : ℝ≥0)) θ hθBound hθMeas)
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hBound n)
