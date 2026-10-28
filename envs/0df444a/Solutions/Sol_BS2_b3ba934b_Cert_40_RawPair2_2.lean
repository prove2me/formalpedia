-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair2_2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T05:48:21.951467+00:00
-- url     : https://prove2.me/submissions/e2d8c32e-5f6e-4f65-a22c-1d879615362a

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair2_2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 2 2) (recipe 2 2)).eval profile2≤10509878689536842271677007430000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair2_2.raw_bound
