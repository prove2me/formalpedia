-- Prove2me | solution 1 for BregmanDistance.three_point_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T14:36:12.572011+00:00
-- url     : https://prove2.me/submissions/bba43231-af38-46de-b657-4b91244c151a

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model


set_option autoImplicit false
open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

-- carved from submission 4d2c4647-a5d0-4c8f-a57b-22839b2fb74b, lines 4110-4123

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (h : H → ℝ) (v y p : H) :
    bregmanD h v y - bregmanD h v p - bregmanD h p y =
      inner ℝ (p - v) (gradient h y - gradient h p) := by
  have he : v-y = (v-p)+(p-y) := by abel
  have hi : inner ℝ (gradient h y) (v-y) =
      inner ℝ (gradient h y) (v-p)+inner ℝ (gradient h y) (p-y) := by
    rw [he,inner_add_right]
  have hc1 : inner ℝ (p-v) (gradient h y) = inner ℝ (gradient h y) (p-v) :=
    real_inner_comm _ _
  have hc2 : inner ℝ (p-v) (gradient h p) = inner ℝ (gradient h p) (p-v) :=
    real_inner_comm _ _
  rw [inner_sub_right,hc1,hc2,← neg_sub v p,inner_neg_right,inner_neg_right]
  dsimp [bregmanD]
  linarith
