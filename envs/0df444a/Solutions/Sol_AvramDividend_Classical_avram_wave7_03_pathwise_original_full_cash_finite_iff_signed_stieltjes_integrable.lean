-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:49:19.952585+00:00
-- url     : https://prove2.me/submissions/a55885f4-3b2f-4e7f-b05f-877e880cbfd0

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

/-- Source exact iff: finite full original ENNReal pre-ruin payout
    on a path is equivalent to integrability of the same-measure
    real discounted Stieltjes density over the same entire domain. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) (q : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) < ⊤ ↔
    IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω))
      (dividendMeasure D ω) := by
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
  constructor
  · intro hCashFinite
    exact hIff.mp (ne_of_lt hCashFinite)
  · intro hInt
    exact lt_top_iff_ne_top.mpr (hIff.mpr hInt)
