-- Prove2me | solution 1 for BregmanDistance.step_fejer_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T14:40:17.922865+00:00
-- url     : https://prove2.me/submissions/88260d49-1214-4698-88f3-f2c27f0f1fe5

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Theorems.Thm_BregmanDistance_monotone_step_bound


set_option autoImplicit false
open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

-- carved from submission 4d2c4647-a5d0-4c8f-a57b-22839b2fb74b, lines 4139-4145

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (T : H → Set H) (h : H → ℝ)
    (hT : IsMonotoneOp T) (z y p : H) (c : ℝ) (hc : 0 < c) (hz : z ∈ zer T)
    (hp : c⁻¹ • (gradient h y - gradient h p) ∈ T p) :
    bregmanD h z p ≤ bregmanD h z y - bregmanD h p y := by
  have ht := BregmanDistance.monotone_step_bound T h hT z 0 y p c hc hz hp
  simp only [inner_zero_left,mul_zero] at ht
  linarith
