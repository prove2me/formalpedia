-- Prove2me | solution 1 for BregmanDistance.monotone_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T14:38:06.798812+00:00
-- url     : https://prove2.me/submissions/a5be3f5f-7fe3-4675-bb90-f3b81a5fcd8d

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Theorems.Thm_BregmanDistance_three_point_identity


set_option autoImplicit false
open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

-- carved from submission 4d2c4647-a5d0-4c8f-a57b-22839b2fb74b, lines 4125-4137

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (T : H → Set H) (h : H → ℝ)
    (hT : IsMonotoneOp T) (v w y p : H) (c : ℝ) (hc : 0 < c) (hw : w ∈ T v)
    (hp : c⁻¹ • (gradient h y - gradient h p) ∈ T p) :
    c * inner ℝ w (p - v) ≤ bregmanD h v y - bregmanD h v p - bregmanD h p y := by
  have hm := hT p v _ w hp hw
  rw [inner_sub_right,inner_smul_right] at hm
  change 0 ≤ c⁻¹*inner ℝ (p-v) (gradient h y-gradient h p)-inner ℝ (p-v) w at hm
  have hm' : inner ℝ (p-v) w ≤ c⁻¹*inner ℝ (p-v) (gradient h y-gradient h p) := by linarith
  have ht := mul_le_mul_of_nonneg_left hm' hc.le
  simp only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] at ht
  rw [BregmanDistance.three_point_identity]
  have he : inner ℝ (p-v) w = inner ℝ w (p-v) := real_inner_comm _ _
  rwa [he] at ht
