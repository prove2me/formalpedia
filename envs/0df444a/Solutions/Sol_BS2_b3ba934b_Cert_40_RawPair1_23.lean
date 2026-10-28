-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_23
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:28:34.856486+00:00
-- url     : https://prove2.me/submissions/cb780530-c265-44ab-9620-7596259533a5

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_23
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 5) (recipe 1 7)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_23.raw_bound
