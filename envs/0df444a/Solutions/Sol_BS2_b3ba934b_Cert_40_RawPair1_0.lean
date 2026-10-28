-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:21:19.45159+00:00
-- url     : https://prove2.me/submissions/b4b95b9b-61e0-4306-ae80-0c5a2498d7d1

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 0) (recipe 1 2)).eval profile1≤5849894674075950384437030000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_0.raw_bound
