-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawOther3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:36:33.106904+00:00
-- url     : https://prove2.me/submissions/cc8c06ed-49e3-4ad7-9145-452424c5c952

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution :
    (∀ i j : Fin 16, i≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)),
∀ coord : Coord 16, valid coord → raw 3 profile3 coord≤rawProfile3 coord) := by
  exact ⟨ThreeBoundMinmaxNumeric.Endpoint16.ordinaryA_checked3, ThreeBoundMinmaxNumeric.Endpoint16.raw_numerical_of_A3⟩
