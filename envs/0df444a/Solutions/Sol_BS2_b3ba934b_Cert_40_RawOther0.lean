-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawOther0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:11:13.337916+00:00
-- url     : https://prove2.me/submissions/aee827ee-bf33-405d-9b4e-9fcb7d11dc81

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution :
    (∀ i j : Fin 40, i≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (rawAExpr 40 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)),
∀ coord : Coord 40, valid coord → raw 0 profile0 coord≤rawProfile0 coord) := by
  exact ⟨ThreeBoundNumeric.Endpoint40.ordinaryA_checked0, ThreeBoundNumeric.Endpoint40.raw_numerical_of_A0⟩
