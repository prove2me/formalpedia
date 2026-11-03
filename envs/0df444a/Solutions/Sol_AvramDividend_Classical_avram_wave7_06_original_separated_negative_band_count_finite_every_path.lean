-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_separated_negative_band_count_finite_every_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:35:48.927834+00:00
-- url     : https://prove2.me/submissions/7fe5731f-befc-47ef-92a6-a60aa1a7f64c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) < ⊤ := by
  classical
  let δ : ℝ := 1 / ((n : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let E : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧ δ ≤ dist (j u) 0}
  have hFin : E.Finite := by
    simpa only [E, j, δ] using
      (avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
        X ω T δ hδ)
  let K : Set ℝ≥0 :=
    {u | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
      j u ≠ 0 ∧ j u ∈ Iic (-δ)}
  have hSub : K ⊆ E := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have huT : u ≤ T := hu.2.2.1
    have huBand : j u ≤ -δ := hu.2.2.2.2
    have huNeg : j u ≤ 0 := by linarith
    have hMag : δ ≤ dist (j u) 0 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonpos huNeg]
      linarith
    exact ⟨hu0, huT, hMag⟩
  have hK : K.Finite := hFin.subset hSub
  change ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ j u ≠ 0}).map (fun u : ℝ≥0 => (u, j u)))
      (Ioc 0 T ×ˢ Iic (-δ)) < ⊤
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
    X ω 0 T (Iic (-δ)) measurableSet_Iic]
  change (K.encard : ENNReal) < ⊤
  obtain ⟨m, hm⟩ := hK.exists_encard_eq_coe
  rw [hm]
  simp

-- W7-06 snapshot validation refresh variant 1; mathematical proof unchanged.
