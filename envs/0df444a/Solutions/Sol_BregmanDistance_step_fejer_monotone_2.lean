-- Prove2me | solution 2 for BregmanDistance.step_fejer_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T14:40:37.266477+00:00
-- url     : https://prove2.me/submissions/b45e0c41-8dd4-4b44-8dbf-cc5faad55f74

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (T : H → Set H) (h : H → ℝ)
    (hT : IsMonotoneOp T) (z y p : H) (c : ℝ) (hc : 0 < c) (hz : z ∈ zer T)
    (hp : c⁻¹ • (gradient h y - gradient h p) ∈ T p) :
    bregmanD h z p ≤ bregmanD h z y - bregmanD h p y := by
  have hm := hT p z _ 0 hp hz
  rw [sub_zero, inner_smul_right] at hm
  have hm' : 0 ≤ inner ℝ (p - z) (gradient h y - gradient h p) := by
    have := mul_nonneg (le_of_lt hc) hm
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
  simp only [bregmanD]
  have e1 : z - y = (z - p) + (p - y) := by abel
  rw [e1, inner_add_right]
  have e2 : inner ℝ (p - z) (gradient h y - gradient h p) =
      inner ℝ (gradient h y) (p - z) - inner ℝ (gradient h p) (p - z) := by
    rw [inner_sub_right, real_inner_comm, real_inner_comm (gradient h p)]
  have e3 : z - p = -(p - z) := by abel
  rw [e3, inner_neg_right, inner_neg_right]
  linarith
