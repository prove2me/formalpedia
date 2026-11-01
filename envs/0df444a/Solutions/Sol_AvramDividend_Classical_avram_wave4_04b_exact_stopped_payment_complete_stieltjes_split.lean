-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_exact_stopped_payment_complete_stieltjes_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:46:30.545139+00:00
-- url     : https://prove2.me/submissions/02b266cd-182d-47a0-bbb1-9a089cc16604

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The exact stopped payment-time window of the genuine dividend Stieltjes
measure splits into true chronological right-payment atoms and all atomless
variation, with the right discount and payment-time indicator at each atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes τ, ENNReal.ofReal (Real.exp (-q * s)) ∂μ) =
      (∑' t : A, μ {(t : ℝ)} *
        (paymentTimes τ).indicator
          (fun s : ℝ => ENNReal.ofReal (Real.exp (-q * s))) (t : ℝ)) +
      (∫⁻ s in paymentTimes τ,
        ENNReal.ofReal (Real.exp (-q * s)) ∂μdiffuse) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  let v : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-q * s))
  let f : ℝ → ℝ≥0∞ := (paymentTimes τ).indicator v
  obtain ⟨A, μatom, μdiffuse, hAcount, hAmeas, hdecomp,
    hsum, hsupport, hnull, hReward⟩ :=
    avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split
      D hD ω T f
  have hMeas : MeasurableSet (paymentTimes τ) :=
    paymentTimes_measurable τ
  have hFormula :
      (∫⁻ s in paymentTimes τ, v s ∂μ) =
      (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
      (∫⁻ s in paymentTimes τ, v s ∂μdiffuse) := by
    change (∫⁻ s : ℝ, f s ∂μ) =
      (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
      (∫⁻ s : ℝ, f s ∂μdiffuse) at hReward
    change (∫⁻ s : ℝ, (paymentTimes τ).indicator v s ∂μ) =
      (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
      (∫⁻ s : ℝ, (paymentTimes τ).indicator v s ∂μdiffuse) at hReward
    rw [lintegral_indicator hMeas] at hReward
    rw [lintegral_indicator hMeas] at hReward
    exact hReward
  refine ⟨A, μatom, μdiffuse, hAcount, hAmeas,
    hdecomp, hsum, hsupport, hnull, ?_⟩
  change (∫⁻ s in paymentTimes τ, v s ∂μ) =
    (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
      (∫⁻ s in paymentTimes τ, v s ∂μdiffuse)
  exact hFormula
