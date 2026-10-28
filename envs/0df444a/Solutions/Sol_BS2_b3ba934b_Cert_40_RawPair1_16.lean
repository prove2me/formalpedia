-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_16
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:31:04.026064+00:00
-- url     : https://prove2.me/submissions/8604120e-8032-4083-bb9a-23f396ede7e4

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_16
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 4) (recipe 1 5)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_16.raw_bound
