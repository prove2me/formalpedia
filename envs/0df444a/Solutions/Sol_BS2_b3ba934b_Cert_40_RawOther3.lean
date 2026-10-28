-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawOther3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T07:27:22.812187+00:00
-- url     : https://prove2.me/submissions/4beca08b-5b5a-4cd6-8d0c-e3caa379ecc1

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution :
    (∀ i j : Fin 40, i≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (rawAExpr 40 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)),
∀ coord : Coord 40, valid coord → raw 3 profile3 coord≤rawProfile3 coord) := by
  exact ⟨ThreeBoundNumeric.Endpoint40.ordinaryA_checked3, ThreeBoundNumeric.Endpoint40.raw_numerical_of_A3⟩
