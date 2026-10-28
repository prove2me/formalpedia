-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_20
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:07:52.333006+00:00
-- url     : https://prove2.me/submissions/bf65469b-6c85-48b9-ab90-8f6cf13a652d

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_20
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 2) (recipe 1 7)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_20.raw_bound
