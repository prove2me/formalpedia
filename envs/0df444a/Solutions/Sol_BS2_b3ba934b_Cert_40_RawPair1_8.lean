-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_8
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:48:33.677991+00:00
-- url     : https://prove2.me/submissions/561ebe78-d910-48d9-b963-bd23ce97bf13

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_8
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 4)).eval profile1≤4440088403177649112679030000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_8.raw_bound
