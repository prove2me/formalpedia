-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair0_4
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:06:29.009991+00:00
-- url     : https://prove2.me/submissions/f6546938-4204-4fd8-8453-82c351dd2174

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_4
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 0 2) (recipe 0 2)).eval profile0≤809387291765886661574000000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair0_4.raw_bound
