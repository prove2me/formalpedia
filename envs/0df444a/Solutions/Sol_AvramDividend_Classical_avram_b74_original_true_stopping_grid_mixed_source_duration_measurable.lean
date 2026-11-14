-- Prove2me | solution 1 for AvramDividend.Classical.avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:50:20.591208+00:00
-- url     : https://prove2.me/submissions/ddc7cca9-1622-4d16-901f-b73ddf9d0995

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual original stopping-grid source increments and elapsed-square energies are measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hsStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (s i ω : WithTop ℝ≥0)))
    (htStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (t i ω : WithTop ℝ≥0)))
    (hLe : ∀ ω i, i ∈ S → s i ω ≤ t i ω) :
    Measurable (fun ω => ∑ i ∈ S,
      (X.X (t i ω) ω - X.X (s i ω) ω -
        (((t i ω - s i ω : ℝ≥0) : ℝ)) * X.c)^2) ∧
    Measurable (fun ω => ∑ i ∈ S,
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2) := by
  classical
  have hJoint : Measurable
      (fun p : ℝ≥0 × Ω => X.X p.1 p.2) :=
    chat04_levy_joint_time_state_measurable X
  have hs (i : ℕ) (hi : i ∈ S) : Measurable (s i) :=
    measurable_coe_nnreal_ennreal_iff.mp (hsStop i hi).measurable'
  have ht (i : ℕ) (hi : i ∈ S) : Measurable (t i) :=
    measurable_coe_nnreal_ennreal_iff.mp (htStop i hi).measurable'
  have hdt (i : ℕ) (hi : i ∈ S) :
      Measurable (fun ω => ((t i ω - s i ω : ℝ≥0) : ℝ)) := by
    have hr : Measurable (fun ω => (t i ω : ℝ) - (s i ω : ℝ)) :=
      ((ht i hi).coe_nnreal_real).sub ((hs i hi).coe_nnreal_real)
    convert hr using 1
    funext ω
    exact NNReal.coe_sub (hLe ω i hi)
  constructor
  · apply Finset.measurable_sum
    intro i hi
    have hXs : Measurable (fun ω : Ω => X.X (s i ω) ω) :=
      hJoint.comp ((hs i hi).prodMk measurable_id)
    have hXt : Measurable (fun ω : Ω => X.X (t i ω) ω) :=
      hJoint.comp ((ht i hi).prodMk measurable_id)
    exact ((hXt.sub hXs).sub ((hdt i hi).mul measurable_const)).pow_const 2
  · apply Finset.measurable_sum
    intro i hi
    exact (hdt i hi).pow_const 2
