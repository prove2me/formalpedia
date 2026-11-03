-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_separated_band_no_early_source_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:36:21.361908+00:00
-- url     : https://prove2.me/submissions/b65b0e4f-7127-405d-86eb-b1b1d1e21dda

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ u : ℝ≥0, 0 < u → u < ε →
        dist (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) 0 <
          1 / ((n : ℝ) + 1) := by
  classical
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  let J : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let E : Set ℝ≥0 :=
    {u | 0 < u ∧ u ≤ 1 ∧
      1 / ((n : ℝ) + 1) ≤ dist (J u) 0}
  have hFin : E.Finite := by
    simpa only [E, J] using
      (avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
        X ω 1 (1 / ((n : ℝ) + 1)) hδ)
  by_cases he : E = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro u hu0 hu1
    change dist (J u) 0 < _
    by_contra hnot
    have huE : u ∈ E := ⟨hu0, le_of_lt hu1, le_of_not_gt hnot⟩
    simpa [he] using huE
  · have hne : E.Nonempty := Set.nonempty_iff_ne_empty.mpr he
    let F : Finset ℝ≥0 := hFin.toFinset
    have hFne : F.Nonempty := by
      obtain ⟨u, hu⟩ := hne
      refine ⟨u, ?_⟩
      simpa [F] using hu
    let e : ℝ≥0 := F.min' hFne
    have heE : e ∈ E := by
      have hm : e ∈ F := Finset.min'_mem F hFne
      simpa [e, F] using hm
    have hepos : 0 < e := heE.1
    refine ⟨min 1 e, lt_min (by norm_num) hepos, ?_⟩
    intro u hu0 huSmall
    change dist (J u) 0 < _
    by_contra hnot
    have hu1 : u ≤ 1 := le_of_lt (lt_of_lt_of_le huSmall (min_le_left _ _))
    have huE : u ∈ E := ⟨hu0, hu1, le_of_not_gt hnot⟩
    have huF : u ∈ F := by simpa [F] using huE
    have hmin : e ≤ u := Finset.min'_le F u huF
    exact (not_lt_of_ge hmin)
      (lt_of_lt_of_le huSmall (min_le_right _ _))

-- W7-06 snapshot validation refresh variant 3; mathematical proof unchanged.
