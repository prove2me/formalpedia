-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_void_iff_intrinsic_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:42:14.438187+00:00
-- url     : https://prove2.me/submissions/d21317cf-625c-4c0a-83af-1a4450a6df99

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A pathwise identification on the genuine original Lévy jump measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    (∀ u : ℝ≥0, u ∈ Ioc 0 T →
      ¬ (X.X u ω + (1 / ((n : ℝ) + 1)) ≤
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ↔
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by
  classical
  let δ : ℝ := 1 / ((n : ℝ) + 1)
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  change (∀ u : ℝ≥0, u ∈ Ioc 0 T →
      ¬ (X.X u ω + δ ≤
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ↔
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u))) (Ioc 0 T ×ˢ Iic (-δ)) = 0
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
    X ω 0 T (Iic (-δ)) measurableSet_Iic]
  change (∀ u : ℝ≥0, u ∈ Ioc 0 T →
      ¬ (X.X u ω + δ ≤
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ↔
    (({u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
      j u ≠ 0 ∧ j u ∈ Iic (-δ)}).encard : ENNReal) = 0
  constructor
  · intro hNo
    have hEmpty :
        {u : ℝ≥0 | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
          j u ≠ 0 ∧ j u ∈ Iic (-δ)} = ∅ := by
      ext u
      constructor
      · intro hu
        have hJump : X.X u ω + δ ≤
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by
          have hj : j u ≤ -δ := hu.2.2.2.2
          dsimp [j] at hj
          linarith
        exact False.elim ((hNo u ⟨hu.2.1, hu.2.2.1⟩) hJump)
      · intro hu
        exact False.elim hu
    rw [hEmpty]
    simp
  · intro hZero u hu hJump
    have hEmpty :
        {v : ℝ≥0 | 0 < v ∧ (0 : ℝ≥0) < v ∧ v ≤ T ∧
          j v ≠ 0 ∧ j v ∈ Iic (-δ)} = ∅ := by
      apply Set.encard_eq_zero.mp
      exact ENat.toENNReal_inj.mp (by simpa using hZero)
    have hjLe : j u ≤ -δ := by
      dsimp [j]
      linarith
    have hjNeg : j u < 0 := lt_of_le_of_lt hjLe (neg_lt_zero.mpr hδ)
    have huMem :
        u ∈ {v : ℝ≥0 | 0 < v ∧ (0 : ℝ≥0) < v ∧ v ≤ T ∧
          j v ≠ 0 ∧ j v ∈ Iic (-δ)} :=
      ⟨hu.1, hu.1, hu.2, ne_of_lt hjNeg, hjLe⟩
    rw [hEmpty] at huMem
    simp at huMem
