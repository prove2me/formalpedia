-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_real_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:51:06.702573+00:00
-- url     : https://prove2.me/submissions/4f8dcee0-6c49-466d-aea3-e8b83532ad74

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact source full Stieltjes signed/ENNReal mean identity for a
    finite nonnegative real-valued random clock, assuming finite payout. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ)
    (hτNonneg : ∀ ω, 0 ≤ τ ω)
    (hτMeas : Measurable τ)
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  let θ : Ω → ℝ≥0 := fun ω => (τ ω).toNNReal
  have hCast (ω : Ω) : (θ ω : ℝ) = τ ω := by
    exact Real.coe_toNNReal (τ ω) (hτNonneg ω)
  have hMeasNN : Measurable (fun ω => (θ ω : ℝ)) := by
    have hFun : (fun ω => (θ ω : ℝ)) = τ := funext hCast
    rw [hFun]
    exact hτMeas
  have hFiniteNN :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤ := by
    simpa only [hCast] using hCashFinite
  have hBridge :=
    avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
      X x C D hD q hq θ hMeasNN hFiniteNN
  simpa only [hCast] using hBridge
