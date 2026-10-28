-- Prove2me | solution 1 for AvramDividend.Classical.esscher_clock_capped_infimum_cdf_product_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:06:11.400421+00:00
-- url     : https://prove2.me/submissions/ab75831b-34a3-4ea5-81a9-ab8b0e734cda

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_stopped_event_laws_agree
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_adapted
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The stopped true-infimum CDF at a real clock agrees under the
random-time Esscher sampling law and the independent terminal clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (a : ℝ)
    {ν : Measure ℝ} [SFinite ν] :
    ((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ))))
      {z : Ω × ℝ | z.2.toNNReal ≤ T ∧
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1} ≤ a} =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν)
      {z : Ω × ℝ | z.2.toNNReal ≤ T ∧
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1} ≤ a} := by
  let E : Set (Ω × ℝ) := {z | z.2.toNNReal ≤ T ∧
    -sInf {y : ℝ | ∃ s : ℝ≥0,
      s ≤ z.2.toNNReal ∧ y = X.X s z.1} ≤ a}
  have hclock : Measurable (fun z : Ω × ℝ => z.2.toNNReal) :=
    measurable_real_toNNReal.comp measurable_snd
  have hp : Measurable (fun z : Ω × ℝ => (z.2.toNNReal, z.1)) :=
    hclock.prodMk measurable_fst
  have hInf : Measurable (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}) :=
    (levy_running_infimum_joint_time_path_measurable X).comp hp
  have hE : MeasurableSet E :=
    (measurableSet_le hclock measurable_const).inter
      (measurableSet_le hInf measurable_const)
  have hSlice (t : ℝ) :
      @MeasurableSet Ω (𝓕 (min t.toNNReal T))
        {ω : Ω | (ω, t) ∈ E} := by
    change @MeasurableSet Ω (𝓕 (min t.toNNReal T))
      {ω : Ω | t.toNNReal ≤ T ∧
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ t.toNNReal ∧ y = X.X s ω} ≤ a}
    by_cases ht : t.toNNReal ≤ T
    · rw [min_eq_left ht]
      have hi := (levy_running_infimum_adapted X t.toNNReal)
      simpa only [ht, true_and] using
        (measurableSet_le hi (measurable_const : Measurable[𝓕 t.toNNReal]
          (fun _ : Ω => a)))
    · have hEmpty :
          {ω : Ω | t.toNNReal ≤ T ∧
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ t.toNNReal ∧ y = X.X s ω} ≤ a} = ∅ := by
                ext ω
                simp [ht]
      rw [hEmpty]
      exact @MeasurableSet.empty Ω (𝓕 (min t.toNNReal T))
  have hSupport : ∀ (ω : Ω) (t : ℝ), (ω, t) ∈ E → t.toNNReal ≤ T := by
    intro ω t he
    exact he.1
  have hJoint :=
    chat04_esscher_likelihood_joint_measurable_of_joint_levy_state X θ
      (chat04_levy_joint_time_state_measurable X)
  exact esscher_clock_supported_stopped_event_laws_agree
    X θ hθ T E hE hSlice hSupport hJoint
