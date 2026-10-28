-- Prove2me | solution 1 for AvramDividend.Classical.chat04_interior_two_sided_initial_safe_window
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:34:50.50936+00:00
-- url     : https://prove2.me/submissions/2d9b68e8-c2ab-4a40-bf7c-4a2786946498

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (hx0 : 0 < x) (hxa : x < a) (ω : Ω) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, t < ε →
        -x ≤ X.X t ω ∧ X.X t ω ≤ a - x := by
  have hc := X.rightCont ω 0
  have hU : Set.Ici (0 : ℝ≥0) = Set.univ := Set.Ici_bot
  rw [hU, continuousWithinAt_univ] at hc
  have hev : ∀ᶠ t in nhds (0 : ℝ≥0), X.X t ω ∈ Set.Ioo (-x) (a - x) :=
    hc.tendsto (by rw [X.X_zero ω]; exact Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨ε, hε, h⟩ := (nhds_bot_basis (α := ℝ≥0)).eventually_iff.1 hev
  exact ⟨ε, hε, fun t ht => ⟨(h ht).1.le, (h ht).2.le⟩⟩
