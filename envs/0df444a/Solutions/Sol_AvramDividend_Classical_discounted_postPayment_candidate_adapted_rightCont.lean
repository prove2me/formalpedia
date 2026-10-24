-- Prove2me | solution 1 for AvramDividend.Classical.discounted_postPayment_candidate_adapted_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:42:38.502723+00:00
-- url     : https://prove2.me/submissions/3229ecde-8cd1-4e0c-909d-2a271c274b7a

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
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) :
    Adapted 𝓕.rightCont
      (fun t ω => Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)) := by
  intro t
  have hW : Measurable[𝓕.rightCont t]
      (fun ω => w (x + X.X t ω - rightLimit D t ω)) :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).2 t
  exact measurable_const.mul hW
