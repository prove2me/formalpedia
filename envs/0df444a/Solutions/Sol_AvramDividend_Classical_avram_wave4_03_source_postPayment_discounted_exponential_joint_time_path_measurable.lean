-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:48:53.875011+00:00
-- url     : https://prove2.me/submissions/80b0d1a1-b834-4bd3-ab03-6228d09008f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Real.exp (θ * (x + X.X z.1 z.2 - rightLimit D z.1 z.2) -
        (z.1 : ℝ) * q)) := by
  have hpath := postPaymentReserve_cadlag_adapted X x D hD
  let F : ℝ≥0 → Ω → ℝ := fun t ω =>
    x + X.X t ω - rightLimit D t ω
  have hFmeas (t : ℝ≥0) : Measurable (F t) := by
    exact (hpath.2.2 t).mono (𝓕.rightCont.le t) le_rfl
  have hFright : ∀ ω t, ContinuousWithinAt
      (fun s : ℝ≥0 => F s ω) (Ici t) t := by
    intro ω t
    exact hpath.1 ω t
  have hFjoint : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation
      F hFmeas hFright
  have htime : Measurable
      (fun z : ℝ≥0 × Ω => (z.1 : ℝ) * q) :=
    (NNReal.continuous_coe.measurable.comp measurable_fst).mul_const q
  change Measurable (fun z : ℝ≥0 × Ω =>
    Real.exp (θ * F z.1 z.2 - (z.1 : ℝ) * q))
  exact ((hFjoint.const_mul θ).sub htime).exp
