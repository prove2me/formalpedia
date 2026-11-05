-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_cap_extension_continuousOn_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:44:03.130221+00:00
-- url     : https://prove2.me/submissions/c3a31fe9-f788-4b76-b92f-61ee9aefdf2f

import Mathlib
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal Topology
noncomputable section

/-- The source cap-linear extension is continuous on all nonnegative reserves. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (hw : ContinuousOn w (Ici (0 : ℝ))) :
    ContinuousOn V (Ici (0 : ℝ)) := by
  by_cases hC : C = ⊤
  · have hEq : V = w := funext (hVtop hC)
    simpa [hEq] using hw
  · have hfront : ∀ z ∈ (Ici (0 : ℝ)) ∩ frontier {y : ℝ | y ≤ C.toReal},
        w z = w C.toReal + (z - C.toReal) := by
      intro z hz
      have hzfront : z ∈ frontier (Iic C.toReal) := hz.2
      rw [frontier_Iic] at hzfront
      have hzc : z = C.toReal := (mem_singleton_iff).mp hzfront
      subst z
      ring
    have hlin : Continuous (fun z : ℝ => w C.toReal + (z - C.toReal)) :=
      continuous_const.add (continuous_id.sub continuous_const)
    have hpiece : ContinuousOn
        (fun z : ℝ => if z ≤ C.toReal then w z else
          w C.toReal + (z - C.toReal)) (Ici (0 : ℝ)) :=
      ContinuousOn.if
        (p := fun z : ℝ => z ≤ C.toReal) hfront
        (hw.mono inter_subset_left)
        hlin.continuousOn
    apply hpiece.congr
    intro z hz
    exact hVfinite hC z
