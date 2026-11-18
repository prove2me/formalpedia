-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_joint_closed_continuous_path_tube_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:39:08.701681+00:00
-- url     : https://prove2.me/submissions/ff85d5e6-f401-4270-bbc4-b53bcb66be85

import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section
/-- Measurability of both original Gaussian Brownian tube constraints on a continuum. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (C(unitInterval, ℝ))]
    [OpensMeasurableSpace (C(unitInterval, ℝ))]
    (B : Ω → C(unitInterval, ℝ)) (hB : Measurable B)
    (T : unitInterval) (r R : ℝ) :
    MeasurableSet {ω | ∀ t : unitInterval, t ≤ T →
      |B ω t| ≤ r ∧ |B ω t + 2 * (t : ℝ)| ≤ R} := by
  let S : Set C(unitInterval, ℝ) :=
    {f | ∀ t : unitInterval, t ≤ T →
      |f t| ≤ r ∧ |f t + 2 * (t : ℝ)| ≤ R}
  have hClosed : IsClosed S := by
    have hEq : S = ⋂ t : {t : unitInterval // t ≤ T},
        {f : C(unitInterval, ℝ) |
          |f t.1| ≤ r ∧ |f t.1 + 2 * (t.1 : ℝ)| ≤ R} := by
      ext f
      simp only [S, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hf t
        exact hf t.1 t.2
      · intro hf t ht
        exact hf ⟨t, ht⟩
    rw [hEq]
    apply isClosed_iInter
    intro t
    apply IsClosed.inter
    · have hUpper : Continuous
          (fun _ : C(unitInterval, ℝ) => (r : ℝ)) := continuous_const
      exact isClosed_le ((continuous_eval_const t.1).abs) hUpper
    · have hCont : Continuous
          (fun f : C(unitInterval, ℝ) =>
            f t.1 + 2 * (t.1 : ℝ)) :=
          (continuous_eval_const t.1).add
            (show Continuous (fun _ : C(unitInterval, ℝ) =>
              (2 : ℝ) * (t.1 : ℝ)) from continuous_const)
      have hUpper : Continuous
          (fun _ : C(unitInterval, ℝ) => (R : ℝ)) := continuous_const
      exact isClosed_le hCont.abs hUpper
  change MeasurableSet (B ⁻¹' S)
  exact hClosed.measurableSet.preimage hB
