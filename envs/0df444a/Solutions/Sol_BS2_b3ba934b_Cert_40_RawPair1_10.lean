-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_10
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:56:23.707934+00:00
-- url     : https://prove2.me/submissions/445c774c-928b-4fb3-bf25-41cbe67d836f

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_10
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 3) (recipe 1 4)).eval profile1≤49108527138416265322304030000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_10.raw_bound
