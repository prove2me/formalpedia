-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:23:23.896273+00:00
-- url     : https://prove2.me/submissions/a68c0f0d-6b88-4080-820b-47bb65c82a6d

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 1) (recipe 1 2)).eval profile1≤5849894674075950384437030000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_1.raw_bound
