-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawOther1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:36:33.127972+00:00
-- url     : https://prove2.me/submissions/a5fcfae6-1045-4063-a8c1-c77d1a1d563c

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution :
    (∀ i j : Fin 16, i≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j)),
∀ coord : Coord 16, valid coord → raw 1 profile1 coord≤rawProfile1 coord) := by
  exact ⟨ThreeBoundMinmaxNumeric.Endpoint16.ordinaryA_checked1, ThreeBoundMinmaxNumeric.Endpoint16.raw_numerical_of_A1⟩
