-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair2_4
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T05:54:11.62309+00:00
-- url     : https://prove2.me/submissions/6da39b10-b061-429c-9c2c-43b8a68a2ed1

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair2_4
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 2 1) (recipe 2 3)).eval profile2≤333228916662993117187787030000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair2_4.raw_bound
