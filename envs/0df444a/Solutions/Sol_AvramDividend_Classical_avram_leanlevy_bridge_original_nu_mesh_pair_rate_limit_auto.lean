-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:51:44.960133+00:00
-- url     : https://prove2.me/submissions/0ee339c7-a69f-4df8-9f1a-52f7e165acee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit
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
      atTop (𝓝 ((((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))) ^ 2) / 2)) := by
  have hν : X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤ := by
    exact avram_p2_a_zero_rate_separated_borel_nu_finite
      X (Iic (-(1 / ((n : ℝ) + 1)))) measurableSet_Iic
      (1 / ((n : ℝ) + 1)) (by positivity) (by intro x hx; exact hx)
  exact avram_leanlevy_bridge_original_nu_mesh_pair_rate_limit X T n hν
