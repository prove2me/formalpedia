-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_grid_occupied_jump_cells_iff_drift_deficits_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:31:40.516194+00:00
-- url     : https://prove2.me/submissions/bdeafc9d-c0f4-44c1-a116-f378870bea77

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_drift_residual_strict_interval_iff_jump

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
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (grid : ℕ → ℝ≥0),
      (∀ i : ℕ, i < n →
        grid i ≤ grid (i + 1) ∧ grid (i + 1) ≤ T) →
      {i : ℕ | i < n ∧ ∃ u : ℝ≥0,
        u ∈ Ioc (grid i) (grid (i + 1)) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} =
      {i : ℕ | i < n ∧
        X.X (grid (i + 1)) ω - X.X (grid i) ω <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ))} := by
  have hSource :=
    avram_wave4_04a_bv_actual_drift_residual_strict_interval_iff_jump
      X hBV hFinite T hT
  filter_upwards [hSource] with ω hω
  intro n grid hGrid
  ext i
  constructor
  · rintro ⟨hi, u, hCell, hJump⟩
    obtain ⟨hst, htT⟩ := hGrid i hi
    have hRes : (grid i : ℝ) * X.drift - X.X (grid i) ω <
        (grid (i + 1) : ℝ) * X.drift -
          X.X (grid (i + 1)) ω :=
      (hω (grid i) (grid (i + 1)) hst htT).mpr
        ⟨u, hCell, hJump⟩
    have hCast : ((grid (i + 1) - grid i : ℝ≥0) : ℝ) =
        (grid (i + 1) : ℝ) - (grid i : ℝ) :=
      NNReal.coe_sub hst
    refine ⟨hi, ?_⟩
    rw [hCast]
    nlinarith
  · rintro ⟨hi, hDef⟩
    obtain ⟨hst, htT⟩ := hGrid i hi
    have hCast : ((grid (i + 1) - grid i : ℝ≥0) : ℝ) =
        (grid (i + 1) : ℝ) - (grid i : ℝ) :=
      NNReal.coe_sub hst
    rw [hCast] at hDef
    have hRes : (grid i : ℝ) * X.drift - X.X (grid i) ω <
        (grid (i + 1) : ℝ) * X.drift -
          X.X (grid (i + 1)) ω := by
      nlinarith
    obtain ⟨u, hCell, hJump⟩ :=
      (hω (grid i) (grid (i + 1)) hst htT).mp hRes
    exact ⟨hi, u, hCell, hJump⟩
