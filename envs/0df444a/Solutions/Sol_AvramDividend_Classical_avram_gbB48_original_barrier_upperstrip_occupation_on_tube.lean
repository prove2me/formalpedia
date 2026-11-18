-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB48_original_barrier_upperstrip_occupation_on_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:30:35.991433+00:00
-- url     : https://prove2.me/submissions/b9564ecb-5937-4702-9114-17c580f60a71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB47_upper_strip_occupation_exact_on_floor_path
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The actual original barrier occupies the entire upper strip on a narrow source tube. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (hTn : (T : ℝ) ≤ n)
    (ω : Ω)
    (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ))
    (hMeas : MeasurableSet {t : ℝ | t < (T : ℝ) ∧
      (5 / 44 : ℝ) <
        riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
          (Real.toNNReal t) ω}) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (T : ℝ) ∧
        (5 / 44 : ℝ) <
          riskProcess X (1 / 8 : ℝ)
            (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
            (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) = (T : ℝ) := by
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  apply avram_gbB47_upper_strip_occupation_exact_on_floor_path
    (n : ℝ) (T : ℝ) (5 / 44 : ℝ) hTreal hTn
    (fun t : ℝ =>
      riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
        (Real.toNNReal t) ω)
  · intro t ht0 htT
    have hst : Real.toNNReal t ≤ T :=
      (Real.toNNReal_le_iff_le_coe).2 (le_of_lt htT)
    exact avram_gbB38_barrier_reserve_above_cutoff_on_tube
      X (Real.toNNReal t) ω
      (fun s hs => hTube s (hs.trans hst))
  · exact hMeas
