-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_nu_mesh_triangular_lintegral_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:19:44.898851+00:00
-- url     : https://prove2.me/submissions/2b88eae4-907a-4b14-9fd2-a2ff30647e7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_equal_mesh_triangular_limit_real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let a : ℝ := (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Tendsto
      (fun m : ℕ => ENNReal.ofReal
        (((m : ℝ) * ((m : ℝ) - 1) / 2) *
          (((T : ℝ) * a) ^ 2 / (m : ℝ) ^ 2)))
      atTop (𝓝 (ENNReal.ofReal (((T : ℝ) * a) ^ 2 / 2))) := by
  dsimp only
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (avram_leanlevy_bridge_original_equal_mesh_triangular_limit_real
      (T : ℝ) (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
