-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_separated_jumps_one_per_short_cell_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:15:48.159182+00:00
-- url     : https://prove2.me/submissions/ed5aec48-ce1c-4e9c-98aa-e68b90f8f705

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_have_uniform_positive_separation_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (grid : ℕ → ℝ≥0),
        (∀ i : ℕ, i < n →
          dist (grid i) (grid (i + 1)) < δ) →
        ∀ i : ℕ, i < n →
        ∀ u v : ℝ≥0,
        (u ≤ T ∧ 0 < u ∧
          X.X u ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) u ≠ 0) →
        (v ≤ T ∧ 0 < v ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0) →
        u ∈ Ioc (grid i) (grid (i + 1)) →
        v ∈ Ioc (grid i) (grid (i + 1)) → u = v := by
  have hSource :=
    avram_wave4_04a_bv_actual_source_jump_times_have_uniform_positive_separation_ae
      X hBV hFinite T hT
  filter_upwards [hSource] with ω hGap
  obtain ⟨δ, hδ, hSep⟩ := hGap
  refine ⟨δ, hδ, ?_⟩
  intro n grid hWidth i hi u v hu hv huCell hvCell
  by_contra hne
  have hSeparated : δ ≤ dist u v := hSep u v hu hv hne
  have hNarrow : dist (grid i) (grid (i + 1)) < δ :=
    hWidth i hi
  have hDistCell : dist u v ≤ dist (grid i) (grid (i + 1)) := by
    have hlu : (grid i : ℝ) < (u : ℝ) := by
      exact_mod_cast huCell.1
    have hlv : (grid i : ℝ) < (v : ℝ) := by
      exact_mod_cast hvCell.1
    have huu : (u : ℝ) ≤ (grid (i + 1) : ℝ) := by
      exact_mod_cast huCell.2
    have hvu : (v : ℝ) ≤ (grid (i + 1) : ℝ) := by
      exact_mod_cast hvCell.2
    have hbounds :
        (grid i : ℝ) ≤ (grid (i + 1) : ℝ) :=
      le_trans (le_of_lt hlu) huu
    have hReal :
        |(u : ℝ) - (v : ℝ)| ≤
          |(grid i : ℝ) - (grid (i + 1) : ℝ)| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hbounds)]
      apply abs_le.mpr
      constructor <;> linarith
    simpa only [NNReal.dist_eq, Real.dist_eq] using hReal
  exact (not_lt_of_ge hSeparated) (lt_of_le_of_lt hDistCell hNarrow)
