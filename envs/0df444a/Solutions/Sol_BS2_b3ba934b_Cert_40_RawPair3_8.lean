-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair3_8
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T07:06:48.57859+00:00
-- url     : https://prove2.me/submissions/54d58767-3e33-4906-ac03-a7fabd490330

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair3_8
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 3 4) (recipe 3 4)).eval profile3≤342172149755249424156185556300000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair3_8.raw_bound
