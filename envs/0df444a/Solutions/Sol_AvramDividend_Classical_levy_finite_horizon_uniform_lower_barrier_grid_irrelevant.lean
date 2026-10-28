-- Prove2me | solution 1 for AvramDividend.Classical.levy_finite_horizon_uniform_lower_barrier_grid_irrelevant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:25:39.249655+00:00
-- url     : https://prove2.me/submissions/7ab35710-2b09-4b2c-8cad-8d0491e83014

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_congr_before_terminal
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- One finite-horizon lower barrier is irrelevant to all sampled capped exits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (z : ℝ) :
    ∃ b : ℝ, ∀ (clock : ℕ → ℝ≥0) (m : ℕ),
      (∀ j : ℕ, j < m → clock j ≤ T) →
      hittingBtwn
        (fun k η => max (X.X (clock k) η - z) (b - X.X (clock k) η))
        (Ioi (0 : ℝ)) 0 m ω =
      hittingBtwn
        (fun k η => X.X (clock k) η - z)
        (Ioi (0 : ℝ)) 0 m ω := by
  obtain ⟨b, hb⟩ := levy_path_bddBelow_finite_horizon X T ω
  refine ⟨b, ?_⟩
  intro clock m hclock
  apply chat03_hittingBtwn_congr_before_terminal
    (fun k η => max (X.X (clock k) η - z) (b - X.X (clock k) η))
    (fun k η => X.X (clock k) η - z) (Ioi (0 : ℝ)) ω m
  intro j hj
  have hmem : X.X (clock j) ω ∈
      {y : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ y = X.X s ω} :=
    ⟨clock j, hclock j hj, rfl⟩
  have hlow : b ≤ X.X (clock j) ω := hb hmem
  have hnot : ¬ (0 : ℝ) < b - X.X (clock j) ω :=
    not_lt.mpr (sub_nonpos.mpr hlow)
  simp only [mem_Ioi, lt_max_iff, hnot, or_false]
