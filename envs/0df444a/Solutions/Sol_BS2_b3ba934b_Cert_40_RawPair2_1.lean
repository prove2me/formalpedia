-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair2_1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T05:45:50.964645+00:00
-- url     : https://prove2.me/submissions/2e0ae560-d99a-4285-bbea-b9e4d9730b85

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair2_1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 2 1) (recipe 2 2)).eval profile2≤439022647791663747058857540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair2_1.raw_bound
