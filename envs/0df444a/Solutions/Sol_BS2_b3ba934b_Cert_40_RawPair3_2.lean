-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair3_2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T06:47:36.635082+00:00
-- url     : https://prove2.me/submissions/3a960ccf-711b-4d6b-be78-6f9cf283819b

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair3_2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 3 2) (recipe 3 3)).eval profile3≤32945822928780164219782456170000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair3_2.raw_bound
