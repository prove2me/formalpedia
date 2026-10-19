-- Prove2me | solution 1 for CohnElkies.normalizedCost_ge_of_no_antiFourierWitness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/a48685b7-4508-4f6c-a7fd-4a6d5b81a0a1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_balancingScale_inv_eq_normalizedCost_mul_sqrt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace ENNReal NNReal
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (f : Admissible d) (hd : 0 < d) (c : ℝ)
    (hno : IsEmpty (AntiFourierWitness d (c * Real.sqrt (d : ℝ)))) :
    c ≤ normalizedCost f := by
  by_contra hnot
  have hcost : normalizedCost f < c := lt_of_not_ge hnot
  have hradius :
      (balancingScale f)⁻¹ ≤ c * Real.sqrt (d : ℝ) := by
    rw [balancingScale_inv_eq_normalizedCost_mul_sqrt f hd]
    exact mul_le_mul_of_nonneg_right hcost.le (Real.sqrt_nonneg _)
  exact hno.false
    ((balancedAntiFourierWitness f hd).monoRadius hradius)
end CohnElkies
