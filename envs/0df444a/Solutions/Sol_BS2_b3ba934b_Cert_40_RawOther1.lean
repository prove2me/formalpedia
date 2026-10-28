-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawOther1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:59:21.736705+00:00
-- url     : https://prove2.me/submissions/a4eee6f2-5b01-4c87-8d57-510f2526186d

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution :
    (∀ i j : Fin 40, i≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (rawAExpr 40 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j)),
∀ coord : Coord 40, valid coord → raw 1 profile1 coord≤rawProfile1 coord) := by
  exact ⟨ThreeBoundNumeric.Endpoint40.ordinaryA_checked1, ThreeBoundNumeric.Endpoint40.raw_numerical_of_A1⟩
