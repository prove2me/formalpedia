-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_33
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:02:29.888428+00:00
-- url     : https://prove2.me/submissions/0a7c58d2-b5cb-49d4-86ed-b3deadc6672f

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_33
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 10)).eval profile1≤37858421375922335576410000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_33.raw_bound
