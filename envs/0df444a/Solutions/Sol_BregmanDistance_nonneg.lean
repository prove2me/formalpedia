-- Prove2me | solution 1 for BregmanDistance.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T14:38:06.132135+00:00
-- url     : https://prove2.me/submissions/603782fc-3d9c-4e52-abe1-1ec91bd3dc2e

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Theorems.Thm_BregmanDistance_gradient_support


set_option autoImplicit false
open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

-- carved from submission 4d2c4647-a5d0-4c8f-a57b-22839b2fb74b, lines 1142-1146

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (S : Set H) (h : H → ℝ)
    (hh : IsBregmanFunction S h) {x y : H} (hx : x ∈ closure S) (hy : y ∈ S) :
    0 ≤ bregmanD h x y := by
  have hs := BregmanDistance.gradient_support S h hh hy hx
  dsimp [bregmanD]
  linarith
