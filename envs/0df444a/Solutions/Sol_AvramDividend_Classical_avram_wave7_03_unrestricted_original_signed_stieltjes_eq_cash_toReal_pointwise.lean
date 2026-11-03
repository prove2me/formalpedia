-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_unrestricted_original_signed_stieltjes_eq_cash_toReal_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:40:44.89421+00:00
-- url     : https://prove2.me/submissions/a58b2f66-a91c-42f7-9e4b-7a56c56e700d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Full original Stieltjes real integral, in Lean's totalised convention,
    equals the toReal of the exact ENNReal payout on every source path.
    If cash is infinite, both totalised reals are zero: this does NOT
    assert IntegrableOn on those paths. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) (q : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal =
      (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  let S : Set ℝ := paymentTimes (ruinTime X x D ω)
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ := fun t => Real.exp (-(q * t))
  have hf : Measurable f := by
    dsimp [f]
    exact Real.continuous_exp.measurable.comp
      ((measurable_const.mul measurable_id).neg)
  have hNN : 0 ≤ᵐ[μ.restrict S] f :=
    Filter.Eventually.of_forall
      (fun t => (Real.exp_pos (-(q * t))).le)
  have hIff :
      ((∫⁻ t in S, ENNReal.ofReal (f t) ∂μ) ≠ ⊤) ↔
      Integrable f (μ.restrict S) :=
    MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hf.aestronglyMeasurable hNN
  by_cases hFinite : (∫⁻ t in S, ENNReal.ofReal (f t) ∂μ) ≠ ⊤
  · have hInt : Integrable f (μ.restrict S) := hIff.mp hFinite
    have hEq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNN
    have hgNN : 0 ≤ ∫ t in S, f t ∂μ := by
      apply integral_nonneg
      intro t
      exact (Real.exp_pos (-(q * t))).le
    change (∫⁻ t in S, ENNReal.ofReal (f t) ∂μ).toReal =
      ∫ t in S, f t ∂μ
    calc
      (∫⁻ t in S, ENNReal.ofReal (f t) ∂μ).toReal =
        (ENNReal.ofReal (∫ t in S, f t ∂μ)).toReal :=
          congrArg ENNReal.toReal hEq.symm
      _ = ∫ t in S, f t ∂μ := ENNReal.toReal_ofReal hgNN
  · have hNotInt : ¬ Integrable f (μ.restrict S) := by
      intro hInt
      exact hFinite (hIff.mpr hInt)
    have hTop : (∫⁻ t in S, ENNReal.ofReal (f t) ∂μ) = ⊤ :=
      not_not.mp hFinite
    have hZero : (∫ t in S, f t ∂μ) = 0 :=
      MeasureTheory.integral_undef hNotInt
    change (∫⁻ t in S, ENNReal.ofReal (f t) ∂μ).toReal =
      ∫ t in S, f t ∂μ
    simp [hTop, hZero]
