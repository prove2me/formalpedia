-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_smalljump_cutoff_support_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:25:13.572828+00:00
-- url     : https://prove2.me/submissions/a86ca522-2f4e-44cc-a7d6-8b91f59d4c55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The intrinsic strict-small negative mark cutoff has a finite original
jump-time support on every compact horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      -1 < X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 2))}.Finite := by
  classical
  let δ : ℝ := 1 / ((n : ℝ) + 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hFinite :=
    avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
      X ω T δ hδ
  change {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ -1 < j u ∧ j u ≤ -δ}.Finite
  apply hFinite.subset
  intro u hu
  rcases hu with ⟨hu0, huT, _, hcut⟩
  have hjnonpos : j u ≤ 0 := by linarith
  have hmag : δ ≤ dist (j u) 0 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonpos hjnonpos]
    linarith
  exact ⟨hu0, huT, hmag⟩
