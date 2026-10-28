-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_22
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:23:52.591604+00:00
-- url     : https://prove2.me/submissions/390625cf-9292-424c-a5ba-f917d4856f12

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_22
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 4) (recipe 1 7)).eval profile1≤45307068002858374123276540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_22.raw_bound
