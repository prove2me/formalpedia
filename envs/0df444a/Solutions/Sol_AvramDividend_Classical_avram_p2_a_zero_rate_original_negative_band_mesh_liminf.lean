-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_negative_band_mesh_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:16:59.219788+00:00
-- url     : https://prove2.me/submissions/8e1f6875-d27a-41f6-8fb1-bf6556d42e51

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_enat_mesh_liminf_casts_to_ennreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- On each actual original càdlàg path, the genuine separated-band jump
count is dominated by the liminf of separated negative mesh increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (ε : ℝ) (hε : 0 < ε) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ≤
    Filter.liminf (fun n : ℕ => (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ∞) : ℝ≥0∞)) atTop := by
  classical
  letI : DecidableEq ℝ≥0 := Classical.decEq _
  let Y : ℝ≥0 → ℝ := fun u => X.X u ω
  let S : Set ℝ≥0 :=
    {u | 0 < u ∧ (0 : ℝ≥0) < u ∧ u ≤ T ∧
      Y u - Function.leftLim Y u ≠ 0 ∧
      Y u - Function.leftLim Y u ∈ Iic (-ε)}
  have hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T := by
    intro u hu
    exact ⟨hu.1, hu.2.2.1⟩
  have hLeft : ∀ u ∈ S,
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)) := by
    intro u hu
    exact tendsto_leftLim_of_tendsto (X.leftLim ω u hu.1)
  have hRight : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u := by
    intro u hu
    exact X.rightCont ω u
  have hJump : ∀ u ∈ S,
      Y u - Function.leftLim Y u ≤ -ε := by
    intro u hu
    exact hu.2.2.2.2
  let grid : ℕ → ℕ∞ := fun n =>
    ((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => Y t -
        Y (t - (T / ((n : ℝ≥0) + 1))) < -ε / 2)).card : ℕ∞)
  have hPath : S.encard ≤ Filter.liminf grid atTop := by
    simpa only [grid] using
      (avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
        Y S T hT ε hε hTimes hLeft hRight hJump)
  have hCast :
      (S.encard : ℝ≥0∞) ≤
        Filter.liminf (fun n => (grid n : ℝ≥0∞)) atTop := by
    calc
      (S.encard : ℝ≥0∞) ≤
          ((Filter.liminf grid atTop : ℕ∞) : ℝ≥0∞) :=
        ENat.toENNReal_mono hPath
      _ = _ := avram_p2_enat_mesh_liminf_casts_to_ennreal grid
  have hCount :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) = (S.encard : ℝ≥0∞) := by
    simpa only [S, Y] using
      (avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
        X ω 0 T (Iic (-ε)) measurableSet_Iic)
  rw [hCount]
  convert hCast using 1
  congr 1
  funext n
  congr 1
  congr 1
  congr 1
  apply Finset.ext
  intro t
  simpa only [Finset.mem_filter, Finset.mem_image, Y]
