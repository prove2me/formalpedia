-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_closed_continuous_path_tube_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:37:48.536132+00:00
-- url     : https://prove2.me/submissions/25969cdb-44b0-4b1e-9d78-6817c8c6ffe3

import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section
/-- Measurability of a closed continuous-path tube over an uncountable time range. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (C(unitInterval, ℝ))]
    [OpensMeasurableSpace (C(unitInterval, ℝ))]
    (B : Ω → C(unitInterval, ℝ)) (hB : Measurable B)
    (T : unitInterval) (r : ℝ) :
    MeasurableSet {ω | ∀ t : unitInterval, t ≤ T → |B ω t| ≤ r} := by
  have hClosed :
      IsClosed {f : C(unitInterval, ℝ) |
        ∀ t : unitInterval, t ≤ T → |f t| ≤ r} := by
    have hEq :
        {f : C(unitInterval, ℝ) |
          ∀ t : unitInterval, t ≤ T → |f t| ≤ r} =
        ⋂ t : {t : unitInterval // t ≤ T},
          {f : C(unitInterval, ℝ) | |f t.1| ≤ r} := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hf t
        exact hf t.1 t.2
      · intro hf t ht
        exact hf ⟨t, ht⟩
    rw [hEq]
    exact isClosed_iInter fun t =>
      isClosed_le ((continuous_eval_const t.1).abs) continuous_const
  change MeasurableSet (B ⁻¹'
    {f : C(unitInterval, ℝ) |
      ∀ t : unitInterval, t ≤ T → |f t| ≤ r})
  exact hClosed.measurableSet.preimage hB
