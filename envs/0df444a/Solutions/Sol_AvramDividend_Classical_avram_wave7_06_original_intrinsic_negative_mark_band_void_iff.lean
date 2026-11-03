-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_mark_band_void_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:24:12.212359+00:00
-- url     : https://prove2.me/submissions/ca033ef9-d4cb-48fb-ae84-a1e80fba6c49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Any measurable negative mark band has zero intrinsic count exactly when no source jump enters it. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (B : Set ℝ)
    (hBm : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ)) :
    (∀ u : ℝ≥0, u ∈ Ioc 0 T →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∉ B) ↔
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) = 0 := by
  classical
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  change (∀ u : ℝ≥0, u ∈ Ioc 0 T → j u ∉ B) ↔
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u))) (Ioc 0 T ×ˢ B) = 0
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
    X ω 0 T B hBm]
  change (∀ u : ℝ≥0, u ∈ Ioc 0 T → j u ∉ B) ↔
    (({u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
      j u ≠ 0 ∧ j u ∈ B}).encard : ENNReal) = 0
  constructor
  · intro hNo
    have hEmpty :
        {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
          j u ≠ 0 ∧ j u ∈ B} = ∅ := by
      ext u
      constructor
      · intro hu
        exact False.elim ((hNo u ⟨hu.2.1, hu.2.2.1⟩) hu.2.2.2.2)
      · intro hu
        exact False.elim hu
    rw [hEmpty]
    simp
  · intro hZero u hu hj
    have hEmpty :
        {v : ℝ≥0 | 0 < v ∧ (0 : ℝ≥0) < v ∧ v ≤ T ∧
          j v ≠ 0 ∧ j v ∈ B} = ∅ := by
      apply Set.encard_eq_zero.mp
      exact ENat.toENNReal_inj.mp (by simpa using hZero)
    have hjNeg : j u < 0 := hBneg hj
    have hjNZ : j u ≠ 0 := ne_of_lt hjNeg
    have huMem :
        u ∈ {v : ℝ≥0 | 0 < v ∧ (0 : ℝ≥0) < v ∧ v ≤ T ∧
          j v ≠ 0 ∧ j v ∈ B} :=
      ⟨hu.1, hu.1, hu.2, hjNZ, hj⟩
    rw [hEmpty] at huMem
    simp at huMem
