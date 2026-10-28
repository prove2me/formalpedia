-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T20:22:42.427301+00:00
-- url     : https://prove2.me/submissions/b12201bf-62c7-4ddf-8c72-f4db042b0126

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0)
    (samples : ℕ → ℝ≥0) (hdense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    (⨆ i : ℕ, if samples i ≤ t then
      ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω) else 0).toReal =
    sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) := by
  classical
  let f : ℝ≥0 → ℝ := fun r => X.X (u + r) ω - X.X u ω
  letI : Nonempty (Set.Icc (0 : ℝ≥0) t) :=
    ⟨⟨0, ⟨le_rfl, zero_le⟩⟩⟩
  have hbimage : BddAbove (f '' Set.Icc (0 : ℝ≥0) t) := by
    obtain ⟨M, hM⟩ := levyPath_bddAbove_Icc X ω (u + t)
    refine ⟨M - X.X u ω, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    have hmem : X.X (u + v) ω ∈
        ((fun s : ℝ≥0 => X.X s ω) '' Set.Icc 0 (u + t)) := by
      refine ⟨u + v, ⟨zero_le, ?_⟩, rfl⟩
      exact add_le_add_right hv.2 u
    have hle : X.X (u + v) ω ≤ M := hM hmem
    exact sub_le_sub_right hle (X.X u ω)
  have hb : BddAbove
      (Set.range (fun s : Set.Icc (0 : ℝ≥0) t => f s.1)) := by
    obtain ⟨M, hM⟩ := hbimage
    refine ⟨M, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hM ⟨s.1, s.2, rfl⟩
  have hfzero : f 0 = 0 := by simp [f]
  have hprefix :
      (⨆ i : ℕ, if samples i ≤ t then
        ENNReal.ofReal (f (samples i)) else 0).toReal =
      ⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1 :=
    avram_ws01e_b_dense_prefix_toReal_eq_genuine_sup
      f (shiftedLevy_increments_right_continuous X ω u) hfzero
      samples hdense hzero t ht hb
  have hraw :
      (⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1) =
        sSup (f '' Set.Icc (0 : ℝ≥0) t) := by
    apply le_antisymm
    · apply ciSup_le
      intro s
      exact le_csSup hbimage ⟨s.1, s.2, rfl⟩
    · apply csSup_le
      · refine ⟨f 0, 0, ⟨le_rfl, zero_le⟩, rfl⟩
      · rintro y ⟨v, hv, rfl⟩
        exact le_ciSup hb ⟨v, hv⟩
  exact hprefix.trans hraw
