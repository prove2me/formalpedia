-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_controlled_postpayment_cap_gradient_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:16:19.081776+00:00
-- url     : https://prove2.me/submissions/be80b565-d7d2-4a27-be27-53ee66f5630e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The actual postpayment capped-interior gradient is jointly measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable (fun z : ℝ≥0 × Ω =>
      if 0 < x + X.X z.1 z.2 - rightLimit D z.1 z.2 ∧
        ENNReal.ofReal (x + X.X z.1 z.2 - rightLimit D z.1 z.2) < C
      then deriv w (x + X.X z.1 z.2 - rightLimit D z.1 z.2)
      else 0) := by
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
  have hgradient :
      Measurable (fun y : ℝ =>
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0) :=
    avram_wave4_04b_measurable_cap_interior_deriv_zero_extension w C hw
  change Measurable (fun z : ℝ≥0 × Ω =>
    (fun y : ℝ =>
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
      (F z.1 z.2))
  exact hgradient.comp hjoint
