-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawPair1_30
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:52:38.501219+00:00
-- url     : https://prove2.me/submissions/9805254d-55b7-4769-a60b-2e8cf2a36720

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RawPair1_30
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution : (rawAExpr 40 caps records (recipe 1 5) (recipe 1 9)).eval profile1≤45306527546439468734521540000000000000000000000000000000000000000000000 := by
  exact ThreeBoundNumeric.Endpoint40.RawPair1_30.raw_bound
