-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_15
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:13:02.714147+00:00
-- url     : https://prove2.me/submissions/bfc48163-75ce-4fff-9ee0-c2dedc2d511f

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_15
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 3) (recipe 1 5)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_15.raw_bound
