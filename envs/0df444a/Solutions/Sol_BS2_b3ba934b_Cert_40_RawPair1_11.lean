-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_11
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:01:02.479707+00:00
-- url     : https://prove2.me/submissions/6f0961d5-ecb6-445b-a1f0-700569668c45

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_11
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 4) (recipe 1 4)).eval profile1≤60742759185095740409372030000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_11.raw_bound
