-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:11:40.152317+00:00
-- url     : https://prove2.me/submissions/fdff0c8b-e7ae-4193-89b3-809fe9e56288

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original post-payment reserve at any right-continuous stopping
time is measurable on the original sample space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable (fun ω => x + X.X (τ ω) ω - rightLimit D (τ ω) ω) := by
  have hτNN : Measurable τ :=
    measurable_coe_nnreal_ennreal_iff.mp hτ.measurable'
  have hXJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hSection : ∀ t : ℝ≥0, Measurable
      (fun ω : Ω => x + X.X t ω - rightLimit D t ω) := by
    intro t
    have hXt : Measurable (fun ω : Ω => X.X t ω) :=
      hXJoint.comp (measurable_const.prodMk measurable_id)
    exact (measurable_const.add hXt).sub
      (dividendStrategy_rightLimit_measurable D hD t)
  have hRight := (postPaymentReserve_cadlag_adapted X x D hD).1
  have hJoint : Measurable (fun z : ℝ≥0 × Ω =>
      x + X.X z.1 z.2 - rightLimit D z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation
      (fun t ω => x + X.X t ω - rightLimit D t ω)
      hSection hRight
  exact hJoint.comp (hτNN.prodMk measurable_id)
