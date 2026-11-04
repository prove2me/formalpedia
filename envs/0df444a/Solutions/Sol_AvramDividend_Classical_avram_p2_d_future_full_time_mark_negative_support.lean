-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_full_time_mark_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:17:14.019684+00:00
-- url     : https://prove2.me/submissions/70cf3f5d-661e-4c35-a457-f6c8dbfd5be0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine source jump measure is carried by negative marks on every
jointly Borel physical time-mark set, not only time-mark rectangles. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (C : Set (ℝ≥0 × ℝ)) (hC : MeasurableSet C) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (C ∩ (Set.univ ×ˢ Iio (0 : ℝ))) := by
  classical
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let S : Set ℝ≥0 := {u | 0 < u ∧ j u ≠ 0}
  let f : ℝ≥0 → ℝ≥0 × ℝ := fun u => (u, j u)
  let V : Set (ℝ≥0 × ℝ) := Set.univ ×ˢ Iio (0 : ℝ)
  have hp : Measurable (fun u : ℝ≥0 => (u, ω)) :=
    measurable_id.prodMk measurable_const
  have hj : Measurable j := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hp
  have hf : Measurable f := measurable_id.prodMk hj
  have hV : MeasurableSet V :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Iio
  have hNeg : ∀ u ∈ S, f u ∈ V := by
    intro u hu
    change 0 < u ∧ j u ≠ 0 at hu
    have hle : j u ≤ 0 :=
      avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hu.1
    have hlt : j u < 0 := lt_of_le_of_ne hle hu.2
    exact ⟨Set.mem_univ u, hlt⟩
  have hPre :
      f ⁻¹' C ∩ S = f ⁻¹' (C ∩ V) ∩ S := by
    ext u
    constructor
    · rintro ⟨huC, huS⟩
      exact ⟨⟨huC, hNeg u huS⟩, huS⟩
    · rintro ⟨⟨huC, _⟩, huS⟩
      exact ⟨huC, huS⟩
  change ((Measure.count.restrict S).map f) C =
    ((Measure.count.restrict S).map f) (C ∩ V)
  rw [Measure.map_apply hf hC, Measure.map_apply hf (hC.inter hV)]
  rw [Measure.restrict_apply (hf hC),
    Measure.restrict_apply (hf (hC.inter hV))]
  exact congrArg (fun U : Set ℝ≥0 => Measure.count U) hPre
