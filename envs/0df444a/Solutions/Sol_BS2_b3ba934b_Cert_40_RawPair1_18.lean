-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_18
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:44:45.606985+00:00
-- url     : https://prove2.me/submissions/64709200-c761-470c-adb7-c8f2ff0faa58

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_18
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 7)).eval profile1≤38398877794827724331410000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_18.raw_bound
