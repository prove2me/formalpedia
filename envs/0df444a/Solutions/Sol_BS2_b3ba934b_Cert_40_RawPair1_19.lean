-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_19
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:53:16.064192+00:00
-- url     : https://prove2.me/submissions/775c4da1-9081-4b9d-9aa6-f39009106c1d

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_19
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 7)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_19.raw_bound
