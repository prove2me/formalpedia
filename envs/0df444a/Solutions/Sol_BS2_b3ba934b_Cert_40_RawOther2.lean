-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawOther2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T06:26:33.535548+00:00
-- url     : https://prove2.me/submissions/b45597f3-b077-407a-b0e1-aaee228f56fa

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution :
    (∀ i j : Fin 40, i≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (rawAExpr 40 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j)),
∀ coord : Coord 40, valid coord → raw 2 profile2 coord≤rawProfile2 coord) := by
  exact ⟨ThreeBoundNumeric.Endpoint40.ordinaryA_checked2, ThreeBoundNumeric.Endpoint40.raw_numerical_of_A2⟩
