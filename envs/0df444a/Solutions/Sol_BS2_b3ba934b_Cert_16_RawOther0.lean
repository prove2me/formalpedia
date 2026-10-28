-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawOther0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:32:35.629121+00:00
-- url     : https://prove2.me/submissions/e50fc9ff-04bb-4a71-a166-03cc3057d30d

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution :
    (∀ i j : Fin 16, i≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)),
∀ coord : Coord 16, valid coord → raw 0 profile0 coord≤rawProfile0 coord) := by
  exact ⟨ThreeBoundMinmaxNumeric.Endpoint16.ordinaryA_checked0, ThreeBoundMinmaxNumeric.Endpoint16.raw_numerical_of_A0⟩
