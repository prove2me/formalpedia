-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess23_original_uniform_grid_ae_eventual_one_jump_per_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:45:00.003142+00:00
-- url     : https://prove2.me/submissions/af4b928b-04d4-4eb7-bde1-a97f35088712

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_separated_jumps_one_per_short_cell_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine cofinal shrinking meshes eventually separate original finite-activity jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0) (cells : ℕ → ℕ)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in (Filter.atTop : Filter ℕ),
        ∀ i : ℕ, i < cells n →
          dist (grid n i) (grid n (i + 1)) < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in (Filter.atTop : Filter ℕ),
      ∀ i : ℕ, i < cells n →
      ∀ u v : ℝ≥0,
      (u ≤ T ∧ 0 < u ∧
        X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0) →
      (v ≤ T ∧ 0 < v ∧
        X.X v ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) v ≠ 0) →
      u ∈ Ioc (grid n i) (grid n (i + 1)) →
      v ∈ Ioc (grid n i) (grid n (i + 1)) → u = v := by
  filter_upwards [avram_wave4_04a_bv_actual_separated_jumps_one_per_short_cell_ae
    X hBV hFinite T hT] with ω hω
  obtain ⟨δ, hδ, hsep⟩ := hω
  filter_upwards [hMesh δ hδ] with n hn
  exact hsep (cells n) (grid n) hn
