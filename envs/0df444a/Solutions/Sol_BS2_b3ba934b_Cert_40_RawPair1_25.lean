-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_25
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:36:19.757064+00:00
-- url     : https://prove2.me/submissions/8e4717b6-58de-4a98-bfb6-8b746f51abf1

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_25
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 9)).eval profile1≤37858421375922335576410000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_25.raw_bound
