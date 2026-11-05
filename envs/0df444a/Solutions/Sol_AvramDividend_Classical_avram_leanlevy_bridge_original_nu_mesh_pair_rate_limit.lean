-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:39:00.113287+00:00
-- url     : https://prove2.me/submissions/7643c81a-446d-4abf-be7e-657576561e42

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_mesh_triangular_lintegral_limit
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_finite_band_rate_square_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (hν : X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤) :
    let a : ℝ := (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Tendsto
      (fun m : ℕ => ENNReal.ofReal
        (((m : ℝ) * ((m : ℝ) - 1) / 2) *
          (((T : ℝ) * a) ^ 2 / (m : ℝ) ^ 2)))
      atTop (𝓝 ((((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))) ^ 2) / 2)) := by
  dsimp only
  rw [← avram_leanlevy_bridge_original_finite_band_rate_square_ennreal X T n hν]
  exact avram_leanlevy_bridge_original_nu_mesh_triangular_lintegral_limit X T n
