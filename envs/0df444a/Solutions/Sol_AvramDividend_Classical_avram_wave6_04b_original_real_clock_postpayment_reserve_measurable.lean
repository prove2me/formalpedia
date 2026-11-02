-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04b_original_real_clock_postpayment_reserve_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:49:25.447423+00:00
-- url     : https://prove2.me/submissions/653e34b9-3982-415f-8194-21bf034c33d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original controlled post-payment reserve is Borel-measurable
as a real-clock path, including the negative-time toNNReal convention. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    Measurable (fun s : ℝ =>
      x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) := by
  have hp := postPaymentReserve_cadlag_adapted X x D hD
  let F : ℝ≥0 → Ω → ℝ := fun t ω =>
    x + X.X t ω - rightLimit D t ω
  have hsections (t : ℝ≥0) : Measurable (F t) := by
    exact (hp.2.2 t).mono (𝓕.rightCont.le t) le_rfl
  have hright : ∀ ω t, ContinuousWithinAt
      (fun s : ℝ≥0 => F s ω) (Ici t) t := by
    intro ω t
    exact hp.1 ω t
  have hjoint : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation F hsections hright
  have hslice : Measurable (fun t : ℝ≥0 => F t ω) := by
    exact hjoint.comp (measurable_id.prodMk measurable_const)
  have hmono : Monotone (fun s : ℝ => s.toNNReal) := by
    intro a b hab
    exact Real.toNNReal_mono hab
  have hclock : Measurable (fun s : ℝ => s.toNNReal) :=
    hmono.measurable
  exact hslice.comp hclock
