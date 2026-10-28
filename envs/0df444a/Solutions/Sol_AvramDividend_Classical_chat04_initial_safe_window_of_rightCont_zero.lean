-- Prove2me | solution 1 for AvramDividend.Classical.chat04_initial_safe_window_of_rightCont_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:53:57.007026+00:00
-- url     : https://prove2.me/submissions/1c1fb715-183b-4aad-9f0a-4c6fc53bb0e4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ha : 0 < a) (ω : Ω)
    (h0 : X.X 0 ω = 0) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, t < ε → -a ≤ X.X t ω := by
  have hc := X.rightCont ω 0
  have hIci : Ici (0 : ℝ≥0) = univ := Set.eq_univ_of_forall fun x => zero_le (a := x)
  rw [hIci, continuousWithinAt_univ] at hc
  have hmem : {t : ℝ≥0 | -a < X.X t ω} ∈ 𝓝 (0 : ℝ≥0) :=
    hc.preimage_mem_nhds (Ioi_mem_nhds (by rw [h0]; linarith))
  obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds hmem ⟨1, one_pos⟩
  exact ⟨u, hu, fun t ht => (hsub ⟨zero_le (a := t), ht⟩).le⟩
