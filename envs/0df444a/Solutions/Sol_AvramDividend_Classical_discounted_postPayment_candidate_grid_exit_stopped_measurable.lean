-- Prove2me | solution 1 for AvramDividend.Classical.discounted_postPayment_candidate_grid_exit_stopped_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:57:20.823772+00:00
-- url     : https://prove2.me/submissions/ca17b0ce-02b4-447a-be2f-04b87a3c3e37

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_grid_exit_stopped_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max
        (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω -
          rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ))) *
        w (x + X.X (clock (K ω)) ω -
          rightLimit D (clock (K ω)) ω)) := by
  obtain ⟨hU, hT⟩ :=
    postPaymentReserve_grid_exit_stopped_measurable
      X x D hD clock H hH lower upper m K hK
  have hw : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hW : Measurable (fun ω =>
      w (x + X.X (clock (K ω)) ω -
        rightLimit D (clock (K ω)) ω)) :=
    hw.comp hU
  have hExponent : Measurable
      (fun ω => -(q * (clock (K ω) : ℝ))) :=
    (measurable_const.mul hT).neg
  have hExp : Measurable
      (fun ω => Real.exp (-(q * (clock (K ω) : ℝ)))) :=
    Real.continuous_exp.measurable.comp hExponent
  exact hExp.mul hW
